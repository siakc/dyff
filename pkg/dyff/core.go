// Copyright © 2019 The Homeport Team
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

package dyff

import (
	"fmt"
	"sort"
	"strings"

	"github.com/gonvenience/bunt"
	"github.com/gonvenience/text"
	"github.com/gonvenience/ytbx"

	yamlv3 "gopkg.in/yaml.v3"
)

// CompareOption sets a specific compare setting for the object comparison
type CompareOption func(*compareSettings)

type compareSettings struct {
	NonStandardIdentifierGuessCountThreshold int
	IgnoreOrderChanges                       bool
	KubernetesEntityDetection                bool
	AdditionalIdentifiers                    []ListItemIdentifierField
}

// ListItemIdentifierField names the field that identifies a list.
type ListItemIdentifierField string

// AdditionalIdentifiers specifies additional identifiers that will be
// used as the key for matcing maps from source to target.
func AdditionalIdentifiers(ids ...string) CompareOption {
	return func(settings *compareSettings) {
		for _, i := range ids {
			settings.AdditionalIdentifiers = append(settings.AdditionalIdentifiers, ListItemIdentifierField(i))
		}
	}
}

// NonStandardIdentifierGuessCountThreshold specifies how many list entries are
// needed for the guess-the-identifier function to actually consider the key
// name. Or in short, if the lists only contain two entries each, there are more
// possibilities to find unique enough key, which might not qualify as such.
func NonStandardIdentifierGuessCountThreshold(nonStandardIdentifierGuessCountThreshold int) CompareOption {
	return func(settings *compareSettings) {
		settings.NonStandardIdentifierGuessCountThreshold = nonStandardIdentifierGuessCountThreshold
	}
}

// IgnoreOrderChanges disables the detection for changes of the order in lists
func IgnoreOrderChanges(value bool) CompareOption {
	return func(settings *compareSettings) {
		settings.IgnoreOrderChanges = value
	}
}

// KubernetesEntityDetection enabled detecting entity identifiers from Kubernetes "kind:" and "metadata:" fields.
func KubernetesEntityDetection(value bool) CompareOption {
	return func(settings *compareSettings) {
		settings.KubernetesEntityDetection = value
	}
}

// CompareInputFiles is one of the convenience main entry points for comparing
// objects. In this case the representation of an input file, which might
// contain multiple documents. It returns a report with the list of differences.
func CompareInputFiles(from ytbx.InputFile, to ytbx.InputFile, compareOptions ...CompareOption) (Report, error) {
	// initialize the comparator with the tool defaults
	cmpr := compare{
		settings: compareSettings{
			NonStandardIdentifierGuessCountThreshold: 3,
			IgnoreOrderChanges:                       false,
			KubernetesEntityDetection:                true,
		},
	}

	// apply the optional compare options provided to this function call
	for _, compareOption := range compareOptions {
		compareOption(&cmpr.settings)
	}

	// in case Kubernetes mode is enabled, try to compare documents in the YAML
	// file by their names rather than just by the order of the documents
	if cmpr.settings.KubernetesEntityDetection {
		var fromDocs, toDocs []*yamlv3.Node
		var fromNames, toNames []string

		for i := range from.Documents {
			if entry := from.Documents[i]; !isEmptyDocument(entry) {
				fromDocs = append(fromDocs, entry)
				if name, err := fqrn(entry.Content[0]); err == nil {
					fromNames = append(fromNames, name)
				}
			}
		}

		for i := range to.Documents {
			if entry := to.Documents[i]; !isEmptyDocument(entry) {
				toDocs = append(toDocs, entry)
				if name, err := fqrn(entry.Content[0]); err == nil {
					toNames = append(toNames, name)
				}
			}
		}

		// when the look-up of a name for each document in each file worked out, it
		// means that the documents are most likely Kubernetes resources, so a comparison
		// using the names can be done, otherwise, leave and continue with default behavior
		if len(fromNames) == len(fromDocs) && len(toNames) == len(toDocs) {
			// Reset the docs and names based on the collected details
			from.Documents, from.Names = fromDocs, fromNames
			to.Documents, to.Names = toDocs, toNames

			// Compare the document nodes, in case of an error it will fall back to the default
			// implementation and continue to compare the files without any special semantics
			if result, err := cmpr.documentNodes(from, to); err == nil {
				return Report{from, to, result}, nil
			}
		}
	}

	if len(from.Documents) != len(to.Documents) {
		return Report{}, fmt.Errorf("comparing YAMLs with a different number of documents is currently not supported")
	}

	var result []Diff
	for idx := range from.Documents {
		diffs, err := cmpr.objects(
			ytbx.Path{
				Root:        &from,
				DocumentIdx: idx,
			},
			from.Documents[idx],
			to.Documents[idx],
		)

		if err != nil {
			return Report{}, err
		}

		result = append(result, diffs...)
	}

	return Report{from, to, result}, nil
}

func nameFromPath(node *yamlv3.Node, field ListItemIdentifierField) (string, error) {
	parts := strings.SplitN(string(field), ".", 2)
	key := parts[0]
	val, err := getValueByKey(node, key)
	if err != nil {
		return "", fmt.Errorf("nameFromPath issue: %w", err)
	}
	if len(parts) == 1 {
		return val.Value, nil
	}
	return nameFromPath(val, ListItemIdentifierField(parts[1]))
}

// AsSequenceNode translates a string list into a SequenceNode
func AsSequenceNode(list []string) *yamlv3.Node {
	result := make([]*yamlv3.Node, len(list))
	for i, entry := range list {
		result[i] = &yamlv3.Node{
			Kind:  yamlv3.ScalarNode,
			Tag:   "!!str",
			Value: entry,
		}
	}

	return &yamlv3.Node{
		Kind:    yamlv3.SequenceNode,
		Content: result,
	}
}

func findOrderChangesInNamedEntryLists(fromNames, toNames []string) []Detail {
	orderchanges := make([]Detail, 0)

	idxLookupMap := make(map[string]int, len(toNames))
	for idx, name := range toNames {
		idxLookupMap[name] = idx
	}

	// Try to find order changes ...
	for idx, name := range fromNames {
		if idxLookupMap[name] != idx {
			orderchanges = append(orderchanges, Detail{
				Kind: ORDERCHANGE,
				From: AsSequenceNode(fromNames),
				To:   AsSequenceNode(toNames),
			})
			break
		}
	}

	return orderchanges
}

func packChangesAndAddToResult(list []Diff, path ytbx.Path, orderchanges []Detail, additions, removals []*yamlv3.Node) ([]Diff, error) {
	// Prepare a diff for this path to added to the result set (if there are changes)
	diff := Diff{Path: &path, Details: []Detail{}}

	if len(orderchanges) > 0 {
		diff.Details = append(diff.Details, orderchanges...)
	}

	if len(removals) > 0 {
		diff.Details = append(diff.Details, Detail{
			Kind: REMOVAL,
			From: &yamlv3.Node{
				Kind:    yamlv3.SequenceNode,
				Tag:     "!!seq",
				Content: removals,
			},
			To: nil,
		})
	}

	if len(additions) > 0 {
		diff.Details = append(diff.Details, Detail{
			Kind: ADDITION,
			From: nil,
			To: &yamlv3.Node{
				Kind:    yamlv3.SequenceNode,
				Tag:     "!!seq",
				Content: additions,
			},
		})
	}

	// If there were changes added to the details list, we can safely add it to
	// the result set. Otherwise it the result set will be returned as-is.
	if len(diff.Details) > 0 {
		list = append([]Diff{diff}, list...)
	}

	return list, nil
}

func followAlias(node *yamlv3.Node) *yamlv3.Node {
	if node != nil && node.Alias != nil {
		return followAlias(node.Alias)
	}

	return node
}

func findValueByKey(mappingNode *yamlv3.Node, key string) (*yamlv3.Node, bool) {
	for i := 0; i < len(mappingNode.Content); i += 2 {
		k, v := followAlias(mappingNode.Content[i]), followAlias(mappingNode.Content[i+1])
		if k.Value == key {
			return v, true
		}
	}

	return nil, false
}

// getValueByKey returns the value for a given key in a provided mapping node,
// or nil with an error if there is no such entry. This is comparable to getting
// a value from a map with `foobar[key]`.
func getValueByKey(mappingNode *yamlv3.Node, key string) (*yamlv3.Node, error) {
	for i := 0; i < len(mappingNode.Content); i += 2 {
		k, v := followAlias(mappingNode.Content[i]), followAlias(mappingNode.Content[i+1])
		if k.Value == key {
			return v, nil
		}
	}

	if names, err := ytbx.ListStringKeys(mappingNode); err == nil {
		return nil, fmt.Errorf("no key '%s' found in map, available keys are: %s", key, strings.Join(names, ", "))
	}

	return nil, fmt.Errorf("no key '%s' found in map and also failed to get a list of key for this map", key)
}

// getEntryFromNamedList returns the entry that is identified by the identifier
// key and a name, for example: `name: one` where name is the identifier key and
// one the name. Function will return nil with bool false if there is no entry.
func getEntryFromNamedList(sequenceNode *yamlv3.Node, identifier ListItemIdentifierField, name string) (*yamlv3.Node, bool) {
	for _, mappingNode := range sequenceNode.Content {
		nodeName, _ := nameFromPath(mappingNode, identifier)
		if nodeName == name {
			return mappingNode, true
		}
	}
	return nil, false
}

// getIdentifierFromKubernetesEntityList returns 'metadata.name' as a field identifier if the provided objects all have the key.
func getIdentifierFromKubernetesEntityList(listA, listB *yamlv3.Node) (ListItemIdentifierField, error) {
	key := ListItemIdentifierField("metadata.name")
	allHaveMetadataName := func(sequenceNode *yamlv3.Node) bool {
		numWithMetadata := 0
		for _, entry := range sequenceNode.Content {
			switch entry.Kind {
			case yamlv3.MappingNode:
				_, err := nameFromPath(entry, key)
				if err == nil {
					numWithMetadata++
				}
			}
		}
		return numWithMetadata == len(sequenceNode.Content)
	}

	listAHasKey := allHaveMetadataName(listA)
	listBHasKey := allHaveMetadataName(listB)
	if listAHasKey && listBHasKey {
		return key, nil
	}

	return "", fmt.Errorf("not all entities appear to have %q fields", key)
}

// fqrn returns something like a fully qualified Kubernetes resource name, which contains its kind, namespace and name
func fqrn(node *yamlv3.Node) (string, error) {
	if node.Kind != yamlv3.MappingNode {
		return "", fmt.Errorf("name look-up for Kubernetes resources does only work with mapping nodes")
	}

	kind, err := nameFromPath(node, "kind")
	if err != nil {
		return "", err
	}

	namespace, err := nameFromPath(node, "metadata.namespace")
	if err != nil {
		namespace = "default"
	}

	name, err := nameFromPath(node, "metadata.name")
	if err != nil {
		return "", err
	}

	return fmt.Sprintf("%s/%s/%s", kind, namespace, name), nil
}

// isEmptyDocument returns true in case the given YAML node is an empty document
func isEmptyDocument(node *yamlv3.Node) bool {
	if node.Kind != yamlv3.DocumentNode {
		return false
	}

	switch len(node.Content) {
	case 1:
		// special case: content is just null (scalar)
		return node.Content[0].Kind == yamlv3.ScalarNode &&
			node.Content[0].Tag == "!!null"
	}

	return false
}

func getNonStandardIdentifierFromNamedLists(listA, listB *yamlv3.Node, nonStandardIdentifierGuessCountThreshold int) ListItemIdentifierField {
	createKeyCountMap := func(list *yamlv3.Node) map[string]int {
		tmp := map[string]map[string]struct{}{}
		for _, entry := range list.Content {
			if entry.Kind != yamlv3.MappingNode {
				return map[string]int{}
			}

			for i := 0; i < len(entry.Content); i += 2 {
				k, v := followAlias(entry.Content[i]), followAlias(entry.Content[i+1])
				if k.Kind == yamlv3.ScalarNode && k.Tag == "!!str" &&
					v.Kind == yamlv3.ScalarNode && v.Tag == "!!str" {
					if _, ok := tmp[k.Value]; !ok {
						tmp[k.Value] = map[string]struct{}{}
					}

					tmp[k.Value][v.Value] = struct{}{}
				}
			}
		}

		result := map[string]int{}
		for key, value := range tmp {
			result[key] = len(value)
		}

		return result
	}

	listALength := len(listA.Content)
	listBLength := len(listB.Content)
	counterA := createKeyCountMap(listA)
	counterB := createKeyCountMap(listB)

	for keyA, countA := range counterA {
		if countB, ok := counterB[keyA]; ok {
			if countA == listALength && countB == listBLength && countA > nonStandardIdentifierGuessCountThreshold {
				return ListItemIdentifierField(keyA)
			}
		}
	}

	return ""
}

func sortNode(node *yamlv3.Node) {
	sort.Slice(node.Content, func(i, j int) bool {
		a, b := node.Content[i], node.Content[j]

		if a.Kind != b.Kind {
			return a.Kind < b.Kind
		}

		if a.Tag != b.Tag {
			return strings.Compare(a.Tag, b.Tag) < 0
		}

		switch a.Kind {
		case yamlv3.ScalarNode:
			return strings.Compare(a.Value, b.Value) < 0
		}

		return len(a.Content) < len(b.Content)
	})
}

func min(a, b int) int {
	if a < b {
		return a
	}

	return b
}

func max(a, b int) int {
	if a > b {
		return a
	}

	return b
}

func isList(node *yamlv3.Node) bool {
	switch node.Kind {
	case yamlv3.SequenceNode:
		return true
	}

	return false
}

// ChangeRoot changes the root of an input file to a position inside its
// document based on the given path. Input files with more than one document are
// not supported, since they could have multiple elements with that path.
func ChangeRoot(inputFile *ytbx.InputFile, path string, useGoPatchPaths bool, translateListToDocuments bool) error {
	multipleDocuments := len(inputFile.Documents) != 1

	if multipleDocuments {
		return fmt.Errorf("change root for an input file is only possible if there is only one document, but %s contains %s",
			inputFile.Location,
			text.Plural(len(inputFile.Documents), "document"))
	}

	// For reference reasons, keep the original root level
	originalRoot := inputFile.Documents[0]

	// Find the object at the given path
	obj, err := ytbx.Grab(inputFile.Documents[0], path)
	if err != nil {
		return err
	}

	wrapInDocumentNodes := func(list []*yamlv3.Node) []*yamlv3.Node {
		result := make([]*yamlv3.Node, len(list))
		for i := range list {
			result[i] = &yamlv3.Node{
				Kind:    yamlv3.DocumentNode,
				Content: []*yamlv3.Node{list[i]},
			}
		}

		return result
	}

	if translateListToDocuments && isList(obj) {
		// Change root of input file main document to a new list of documents based on the the list that was found
		inputFile.Documents = wrapInDocumentNodes(obj.Content)

	} else {
		// Change root of input file main document to the object that was found
		inputFile.Documents = wrapInDocumentNodes([]*yamlv3.Node{obj})
	}

	// Parse path string and create nicely formatted output path
	if resolvedPath, err := ytbx.ParsePathString(path, originalRoot); err == nil {
		path = pathToString(&resolvedPath, useGoPatchPaths, multipleDocuments)
	}

	inputFile.Note = fmt.Sprintf("YAML root was changed to %s", path)

	return nil
}

func pathToString(path *ytbx.Path, useGoPatchPaths bool, showPathRoot bool) string {
	var result string

	if useGoPatchPaths {
		result = styledGoPatchPath(path)

	} else {
		result = styledDotStylePath(path)
	}

	if path != nil && showPathRoot {
		result += bunt.Sprintf("  LightSteelBlue{(%s)}", path.RootDescription())
	}

	return result
}
