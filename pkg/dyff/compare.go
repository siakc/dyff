// Copyright © 2023 The Homeport Team
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
	"strings"

	"github.com/gonvenience/wrap"
	"github.com/gonvenience/ytbx"
	"github.com/mitchellh/hashstructure"
	yamlv3 "gopkg.in/yaml.v3"
)

type compare struct {
	settings compareSettings
}

func (compare *compare) objects(path ytbx.Path, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	switch {
	case from == nil && to == nil:
		return []Diff{}, nil

	case (from == nil && to != nil) || (from != nil && to == nil):
		return []Diff{{
			&path,
			[]Detail{{
				Kind: MODIFICATION,
				From: from,
				To:   to,
			}},
		}}, nil

	case (from.Kind != to.Kind) || (from.Tag != to.Tag):
		return []Diff{{
			&path,
			[]Detail{{
				Kind: MODIFICATION,
				From: from,
				To:   to,
			}},
		}}, nil
	}

	return compare.nonNilSameKindNodes(path, from, to)
}

func (compare *compare) nonNilSameKindNodes(path ytbx.Path, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	var diffs []Diff
	var err error

	switch from.Kind {
	case yamlv3.DocumentNode:
		diffs, err = compare.objects(path, from.Content[0], to.Content[0])

	case yamlv3.MappingNode:
		diffs, err = compare.mappingNodes(path, from, to)

	case yamlv3.SequenceNode:
		diffs, err = compare.sequenceNodes(path, from, to)

	case yamlv3.ScalarNode:
		switch from.Tag {
		case "!!str":
			diffs, err = compare.nodeValues(path, from, to)

		case "!!null":
			// Ignore different ways to define a null value

		default:
			if from.Value != to.Value {
				diffs, err = []Diff{{
					&path,
					[]Detail{{
						Kind: MODIFICATION,
						From: from,
						To:   to,
					}},
				}}, nil
			}
		}

	case yamlv3.AliasNode:
		diffs, err = compare.objects(path, from.Alias, to.Alias)

	default:
		err = fmt.Errorf("failed to compare objects due to unsupported kind %v", from.Kind)
	}

	return diffs, err
}

func (compare *compare) documentNodes(from, to ytbx.InputFile) ([]Diff, error) {
	var result []Diff

	type doc struct {
		node *yamlv3.Node
		idx  int
	}

	var createDocumentLookUpMap = func(inputFile ytbx.InputFile) (map[string]doc, []string, error) {
		var lookUpMap = make(map[string]doc)
		var names []string

		for i, document := range inputFile.Documents {
			node := document.Content[0]

			name, err := fqrn(node)
			if err != nil {
				return nil, nil, err
			}

			names = append(names, name)
			lookUpMap[name] = doc{idx: i, node: node}
		}

		return lookUpMap, names, nil
	}

	fromLookUpMap, fromNames, err := createDocumentLookUpMap(from)
	if err != nil {
		return nil, err
	}

	toLookUpMap, toNames, err := createDocumentLookUpMap(to)
	if err != nil {
		return nil, err
	}

	removals := []*yamlv3.Node{}
	additions := []*yamlv3.Node{}

	for _, name := range fromNames {
		var fromItem = fromLookUpMap[name]
		if toItem, ok := toLookUpMap[name]; ok {
			// `from` and `to` contain the same `key` -> require comparison
			diffs, err := compare.objects(
				ytbx.Path{Root: &from, DocumentIdx: fromItem.idx},
				followAlias(fromItem.node),
				followAlias(toItem.node),
			)

			if err != nil {
				return nil, err
			}

			result = append(result, diffs...)

		} else {
			// `from` contain the `key`, but `to` does not -> removal
			removals = append(removals, fromItem.node)
		}
	}

	for _, name := range toNames {
		var toItem = toLookUpMap[name]
		if _, ok := fromLookUpMap[name]; !ok {
			// `to` contains a `key` that `from` does not have -> addition
			additions = append(additions, toItem.node)
		}
	}

	diff := Diff{Details: []Detail{}}

	if len(removals) > 0 {
		diff.Details = append(diff.Details,
			Detail{
				Kind: REMOVAL,
				From: &yamlv3.Node{
					Kind:    yamlv3.DocumentNode,
					Content: removals,
				},
				To: nil,
			},
		)
	}

	if len(additions) > 0 {
		diff.Details = append(diff.Details,
			Detail{
				Kind: ADDITION,
				From: nil,
				To: &yamlv3.Node{
					Kind:    yamlv3.DocumentNode,
					Content: additions,
				},
			},
		)
	}

	if !compare.settings.IgnoreOrderChanges && len(fromNames) == len(toNames) {
		for i := range fromNames {
			if fromNames[i] != toNames[i] {
				diff.Details = append(diff.Details, Detail{
					Kind: ORDERCHANGE,
					From: AsSequenceNode(fromNames),
					To:   AsSequenceNode(toNames),
				})
				break
			}
		}
	}

	if len(diff.Details) > 0 {
		result = append([]Diff{diff}, result...)
	}

	return result, nil
}

func (compare *compare) mappingNodes(path ytbx.Path, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	result := make([]Diff, 0)
	removals := []*yamlv3.Node{}
	additions := []*yamlv3.Node{}

	for i := 0; i < len(from.Content); i += 2 {
		key, fromItem := from.Content[i], from.Content[i+1]
		if toItem, ok := findValueByKey(to, key.Value); ok {
			// `from` and `to` contain the same `key` -> require comparison
			diffs, err := compare.objects(
				ytbx.NewPathWithNamedElement(path, key.Value),
				followAlias(fromItem),
				followAlias(toItem),
			)

			if err != nil {
				return nil, err
			}

			result = append(result, diffs...)

		} else {
			// `from` contain the `key`, but `to` does not -> removal
			removals = append(removals, key, fromItem)
		}
	}

	for i := 0; i < len(to.Content); i += 2 {
		key, toItem := to.Content[i], to.Content[i+1]
		if _, ok := findValueByKey(from, key.Value); !ok {
			// `to` contains a `key` that `from` does not have -> addition
			additions = append(additions, key, toItem)
		}
	}

	diff := Diff{Path: &path, Details: []Detail{}}

	if len(removals) > 0 {
		diff.Details = append(diff.Details,
			Detail{
				Kind: REMOVAL,
				From: &yamlv3.Node{
					Kind:    from.Kind,
					Tag:     from.Tag,
					Content: removals,
				},
				To: nil,
			},
		)
	}

	if len(additions) > 0 {
		diff.Details = append(diff.Details,
			Detail{
				Kind: ADDITION,
				From: nil,
				To: &yamlv3.Node{
					Kind:    to.Kind,
					Tag:     to.Tag,
					Content: additions,
				},
			},
		)
	}

	if len(diff.Details) > 0 {
		result = append([]Diff{diff}, result...)
	}

	return result, nil
}

func (compare *compare) sequenceNodes(path ytbx.Path, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	// Bail out quickly if there is nothing to check
	if len(from.Content) == 0 && len(to.Content) == 0 {
		return []Diff{}, nil
	}

	if identifier, err := compare.getIdentifierFromNamedLists(from, to); err == nil {
		return compare.namedEntryLists(path, identifier, from, to)
	}

	if identifier := getNonStandardIdentifierFromNamedLists(from, to, compare.settings.NonStandardIdentifierGuessCountThreshold); identifier != "" {
		d, err := compare.namedEntryLists(path, identifier, from, to)
		if err != nil {
			return nil, fmt.Errorf("sequenceNodes(nonstd): %w", err)
		}

		return d, nil
	}

	if compare.settings.KubernetesEntityDetection {
		if identifier, err := getIdentifierFromKubernetesEntityList(from, to); err == nil {
			return compare.namedEntryLists(path, identifier, from, to)
		}
	}

	return compare.simpleLists(path, from, to)
}

func (compare *compare) simpleLists(path ytbx.Path, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	removals := make([]*yamlv3.Node, 0)
	additions := make([]*yamlv3.Node, 0)

	fromLength := len(from.Content)
	toLength := len(to.Content)

	// Special case if both lists only contain one entry, then directly compare
	// the two entries with each other
	if fromLength == 1 && fromLength == toLength {
		return compare.objects(
			ytbx.NewPathWithIndexedListElement(path, 0),
			followAlias(from.Content[0]),
			followAlias(to.Content[0]),
		)
	}

	fromLookup := compare.createLookUpMap(from)
	toLookup := compare.createLookUpMap(to)

	// Fill two lists with the hashes of the entries of each list
	fromCommon := make([]*yamlv3.Node, 0, fromLength)
	toCommon := make([]*yamlv3.Node, 0, toLength)

	for idxPos, fromValue := range from.Content {
		hash := compare.calcNodeHash(fromValue)
		_, ok := toLookup[hash]
		if ok {
			fromCommon = append(fromCommon, fromValue)
		}

		switch {
		case !ok:
			// `from` entry does not exist in `to` list
			removals = append(removals, from.Content[idxPos])

		case len(fromLookup[hash]) > len(toLookup[hash]):
			// `from` entry exists in `to` list, but there are duplicates and
			// the number of duplicates is smaller
			if !compare.hasEntry(removals, from.Content[idxPos]) {
				for i := 0; i < len(fromLookup[hash])-len(toLookup[hash]); i++ {
					removals = append(removals, from.Content[idxPos])
				}
			}
		}
	}

	for idxPos, toValue := range to.Content {
		hash := compare.calcNodeHash(toValue)
		_, ok := fromLookup[hash]
		if ok {
			toCommon = append(toCommon, toValue)
		}

		switch {
		case !ok:
			// `to` entry does not exist in `from` list
			additions = append(additions, to.Content[idxPos])

		case len(fromLookup[hash]) < len(toLookup[hash]):
			// `to` entry exists in `from` list, but there are duplicates and
			// the number of duplicates is increased
			if !compare.hasEntry(additions, to.Content[idxPos]) {
				for i := 0; i < len(toLookup[hash])-len(fromLookup[hash]); i++ {
					additions = append(additions, to.Content[idxPos])
				}
			}
		}
	}

	var orderChanges []Detail
	if !compare.settings.IgnoreOrderChanges {
		orderChanges = compare.findOrderChangesInSimpleList(fromCommon, toCommon)
	}

	return packChangesAndAddToResult([]Diff{}, path, orderChanges, additions, removals)
}

func (compare *compare) namedEntryLists(path ytbx.Path, identifier ListItemIdentifierField, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	removals := make([]*yamlv3.Node, 0)
	additions := make([]*yamlv3.Node, 0)

	result := make([]Diff, 0)

	// Fill two lists with the names of the entries that are common in both lists
	fromLength := len(from.Content)
	fromNames := make([]string, 0, fromLength)
	toNames := make([]string, 0, fromLength)

	// Find entries that are common to both lists to compare them separately, and
	// find entries that are only in from, but not to and are therefore removed
	for _, fromEntry := range from.Content {
		name, err := nameFromPath(fromEntry, identifier)
		if err != nil {
			return nil, fmt.Errorf("nameEntryList from issue: %w", err)
		}

		if toEntry, ok := getEntryFromNamedList(to, identifier, name); ok {
			// `from` and `to` have the same entry identified by identifier and name -> require comparison
			diffs, err := compare.objects(
				ytbx.NewPathWithNamedListElement(path, identifier, name),
				followAlias(fromEntry),
				followAlias(toEntry),
			)
			if err != nil {
				return nil, err
			}
			result = append(result, diffs...)
			fromNames = append(fromNames, name)

		} else {
			// `from` has an entry (identified by identifier and name), but `to` does not -> removal
			removals = append(removals, fromEntry)
		}
	}

	// Find entries that are only in to, but not from and are therefore added
	for _, toEntry := range to.Content {
		name, err := nameFromPath(toEntry, identifier)
		if err != nil {
			return nil, fmt.Errorf("nameEntryList to issue: %w", err)
		}

		if _, ok := getEntryFromNamedList(from, identifier, name); ok {
			// `to` and `from` have the same entry identified by identifier and name (comparison already covered by previous range)
			toNames = append(toNames, name)

		} else {
			// `to` has an entry (identified by identifier and name), but `from` does not -> addition
			additions = append(additions, toEntry)
		}
	}

	var orderChanges []Detail
	if !compare.settings.IgnoreOrderChanges {
		orderChanges = findOrderChangesInNamedEntryLists(fromNames, toNames)
	}

	return packChangesAndAddToResult(result, path, orderChanges, additions, removals)
}

func (compare *compare) nodeValues(path ytbx.Path, from *yamlv3.Node, to *yamlv3.Node) ([]Diff, error) {
	result := make([]Diff, 0)
	if strings.Compare(from.Value, to.Value) != 0 {
		result = append(result, Diff{
			&path,
			[]Detail{{
				Kind: MODIFICATION,
				From: from,
				To:   to,
			}},
		})
	}

	return result, nil
}

func (compare *compare) findOrderChangesInSimpleList(fromCommon, toCommon []*yamlv3.Node) []Detail {
	// Try to find order changes ...
	if len(fromCommon) == len(toCommon) {
		for idx := range fromCommon {
			if compare.calcNodeHash(fromCommon[idx]) != compare.calcNodeHash(toCommon[idx]) {
				return []Detail{{
					Kind: ORDERCHANGE,
					From: &yamlv3.Node{Kind: yamlv3.SequenceNode, Content: fromCommon},
					To:   &yamlv3.Node{Kind: yamlv3.SequenceNode, Content: toCommon},
				}}
			}
		}
	}

	return []Detail{}
}

// hasEntry returns whether the given node is in the provided list. Not exactly
// a fast or efficient way to verify that a node is already in a list, but
// given that this should rarely be used it is ok for now.
func (compare *compare) hasEntry(list []*yamlv3.Node, searchEntry *yamlv3.Node) bool {
	var searchEntryHash = compare.calcNodeHash(searchEntry)
	for _, listEntry := range list {
		if searchEntryHash == compare.calcNodeHash(listEntry) {
			return true
		}
	}

	return false
}

func (compare *compare) listItemIdentifierCandidates() []ListItemIdentifierField {
	// Set default candidates that are most widly used
	var candidates = []ListItemIdentifierField{"name", "key", "id"}

	// Add user supplied additional candidates (taking precedence over defaults)
	candidates = append(compare.settings.AdditionalIdentifiers, candidates...)

	// Add Kubernetes specific extra candidate
	if compare.settings.KubernetesEntityDetection {
		candidates = append(candidates, "manager")
	}

	return candidates
}

func (compare *compare) getIdentifierFromNamedLists(listA, listB *yamlv3.Node) (ListItemIdentifierField, error) {
	isCandidate := func(node *yamlv3.Node) bool {
		if node.Kind == yamlv3.ScalarNode {
			for _, entry := range compare.listItemIdentifierCandidates() {
				if node.Value == string(entry) {
					return true
				}
			}
		}

		return false
	}

	createKeyCountMap := func(sequenceNode *yamlv3.Node) map[ListItemIdentifierField]map[string]struct{} {
		result := map[ListItemIdentifierField]map[string]struct{}{}
		for _, entry := range sequenceNode.Content {
			switch entry.Kind {
			case yamlv3.MappingNode:
				for i := 0; i < len(entry.Content); i += 2 {
					k, v := followAlias(entry.Content[i]), followAlias(entry.Content[i+1])
					if isCandidate(k) {
						if _, found := result[ListItemIdentifierField(k.Value)]; !found {
							result[ListItemIdentifierField(k.Value)] = map[string]struct{}{}
						}

						result[ListItemIdentifierField(k.Value)][v.Value] = struct{}{}
					}
				}
			}
		}

		return result
	}

	counterA := createKeyCountMap(listA)
	counterB := createKeyCountMap(listB)

	// Check for the usual suspects: name, key, and id
	for _, identifier := range compare.listItemIdentifierCandidates() {
		if countA, okA := counterA[identifier]; okA && len(countA) == len(listA.Content) {
			if countB, okB := counterB[identifier]; okB && len(countB) == len(listB.Content) {
				return identifier, nil
			}
		}
	}

	return "", fmt.Errorf("unable to find a key that can serve as an unique identifier")
}

func (compare *compare) createLookUpMap(sequenceNode *yamlv3.Node) map[uint64][]int {
	result := make(map[uint64][]int, len(sequenceNode.Content))
	for idx, entry := range sequenceNode.Content {
		hash := compare.calcNodeHash(entry)
		if _, ok := result[hash]; !ok {
			result[hash] = []int{}
		}

		result[hash] = append(result[hash], idx)
	}

	return result
}

func (compare *compare) basicType(node *yamlv3.Node) interface{} {
	switch node.Kind {
	case yamlv3.DocumentNode:
		panic("document nodes are not supported to be translated into a basic type")

	case yamlv3.MappingNode:
		result := map[interface{}]interface{}{}
		for i := 0; i < len(node.Content); i += 2 {
			k, v := followAlias(node.Content[i]), followAlias(node.Content[i+1])
			result[compare.basicType(k)] = compare.basicType(v)
		}

		return result

	case yamlv3.SequenceNode:
		result := []interface{}{}

		if compare.settings.IgnoreOrderChanges {
			sortNode(node)
		}

		for _, entry := range node.Content {
			result = append(result, compare.basicType(followAlias(entry)))
		}

		return result

	case yamlv3.ScalarNode:
		return node.Value

	case yamlv3.AliasNode:
		return compare.basicType(node.Alias)

	default:
		panic("should be unreachable")
	}
}

func (compare *compare) calcNodeHash(node *yamlv3.Node) (hash uint64) {
	var err error

	switch node.Kind {
	case yamlv3.MappingNode, yamlv3.SequenceNode:
		hash, err = hashstructure.Hash(compare.basicType(node), nil)

	case yamlv3.ScalarNode:
		hash, err = hashstructure.Hash(node.Value, nil)

	case yamlv3.AliasNode:
		hash = compare.calcNodeHash(followAlias(node))

	default:
		err = fmt.Errorf("kind %v is not supported", node.Kind)
	}

	if err != nil {
		panic(wrap.Errorf(err, "failed to calculate hash of %#v", node.Value))
	}

	return hash
}
