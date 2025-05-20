import re
import sys
from graphviz import Digraph

def parse_coq_file(filepath):
    with open(filepath, 'r') as f:
        lines = f.readlines()

    elements = {}
    pattern = re.compile(r'^(Definition|Inductive|Lemma|Theorem)\s+(\w+)')
    current = None
    in_proof = False

    for line in lines:
        stripped = line.strip()

        match = pattern.match(stripped)
        if match and not in_proof:
            if current:
                elements[current['name']] = current
            kind, name = match.groups()
            current = {'type': kind, 'name': name, 'lines': [line]}
            continue

        if current:
            current['lines'].append(line)

            if stripped.startswith("Proof"):
                in_proof = True
            if stripped in ["Qed.", "Admitted."] or stripped.endswith("Qed.") or stripped.endswith("Admitted."):
                in_proof = False
                elements[current['name']] = current
                current = None

    # Final element if file doesn't end in Qed
    if current:
        elements[current['name']] = current

    # Build dependencies
    for name, element in elements.items():
        full_text = " ".join(element['lines'])
        element['deps'] = set()
        for other_name in elements:
            if other_name == name:
                continue
            if re.search(r'\b' + re.escape(other_name) + r'\b', full_text):
                element['deps'].add(other_name)

    return elements

def create_graph(elements, output_file='dependency_graph'):
    dot = Digraph(format='png')

    color_map = {
        'Theorem': 'cyan',
        'Lemma': 'green',
        'Definition': 'red',
        'Inductive': 'red'
    }

    for name, info in elements.items():
        color = color_map.get(info['type'], 'black')
        dot.node(name, label=name, fontcolor=color)

    for name, info in elements.items():
        for dep in info['deps']:
            dot.edge(name, dep)

    dot.render(output_file, cleanup=True)
    print(f"Graph rendered to {output_file}.png")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python coq_dep_graph.py <file.v> <output_name>")
        sys.exit(1)

    coq_file = sys.argv[1]
    output_name = sys.argv[2]
    elements = parse_coq_file(coq_file)
    create_graph(elements, output_name)
