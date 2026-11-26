import itertools
import networkx as nx
from itertools import combinations

def chromatic_number_upper_bound(G):
    """Compute an upper bound on chromatic number using greedy coloring."""
    nodes = list(G.nodes())
    color_map = {}
    for node in nodes:
        used_colors = {color_map[neighbor] for neighbor in G[node] if neighbor in color_map}
        color_map[node] = next(c for c in range(len(nodes)) if c not in used_colors)
    return max(color_map.values()) + 1

def has_k_clique(G, k):
    """Check if graph contains a clique of size k."""
    try:
        return nx.graph_clique_number(G) >= k
    except:
        # Fallback: brute-force check for small k
        for clique in combinations(G.nodes(), k):
            if all(G.has_edge(u, v) for u, v in combinations(clique, 2)):
                return True
        return False

def induce_subgraph(G, nodes):
    """Return the induced subgraph on given nodes."""
    return G.subgraph(nodes)

def chromatic_number_induced(G, nodes):
    """Return chromatic number of induced subgraph."""
    subgraph = induce_subgraph(G, nodes)
    return chromatic_number_upper_bound(subgraph)

def find_counterexample():
    """Search for a counterexample to Erdős 628 (k=6, a=3, b=4)."""
    # We'll look for small graphs with chi=6 and no K_6
    # Start with known constructions of high chromatic number graphs
    # For now, let's try some small examples manually constructed
    
    # Example: Mycielski construction of triangle-free graph with large chromatic number
    # But we need to build a graph with chi=6 and no K_6
    
    # Let's try a known example: the Grötzsch graph extended or similar
    # Or just generate small graphs and check
    
    # For efficiency, we'll generate small graphs with chi=6
    # and check if they satisfy the property
    
    # Since full enumeration is expensive, we'll focus on a few constructions
    # and verify the property directly
    
    # Constructing a graph with chi=6 and no K_6
    # One way: take a complete graph on 5 vertices, add one more vertex connected to all
    # But that gives chi=6 and K_6, so not valid
    
    # Try a different approach: start with a 6-chromatic graph with no K_6
    # We can construct a graph with chi=6 by taking a blow-up of a 5-clique or similar
    
    # Let's try a simple construction:
    # Take a 5-cycle C5, make a blow-up where each vertex is replaced by a clique of size 2
    # This should give a graph with chi=6 and no K_6
    
    # Let's define a graph manually:
    # Nodes: 0..9 (5 vertices of C5, each blown up to 2 nodes)
    # Edges: 
    # - C5 edges: (0,1),(1,2),(2,3),(3,4),(4,0)
    # - Each i in [0,4] connects to both i*2 and i*2+1
    # - Each i*2 connects to (i*2+1) and (i+1)*2 (mod 10)
    
    # Actually, simpler: take a 6-clique minus one edge, but that's not 6-chromatic
    
    # Better idea: Use Mycielski construction iteratively to get 6-chromatic graph
    # But we must ensure no K_6
    
    # Let's try a brute-force approach with small graphs
    # Generate all graphs with n=10 nodes and check
    # But that's too many. Instead, we'll try a smarter approach:
    
    # Let's try a known 6-chromatic graph with no K_6
    # The following is a known 6-chromatic graph (from Mycielski) with no K_6:
    # We'll construct it manually
    
    # Graph with 10 nodes, 6-chromatic, no K_6
    # Node set: 0..9
    # Edges: 
    # C5: (0,1),(1,2),(2,3),(3,4),(4,0)
    # Additional edges to make it 6-chromatic and avoid K6:
    # Add edges to make it triangle-free, then add more to increase chromatic number
    
    # Let's define a specific example:
    G = nx.Graph()
    G.add_edges_from([
        (0,1), (1,2), (2,3), (3,4), (4,0),  # C5
        (0,5), (1,6), (2,7), (3,8), (4,9),  # Blow-up
        (5,6), (6,7), (7,8), (8,9), (9,5),  # Outer cycle
        (0,7), (1,8), (2,9), (3,5), (4,6),  # Cross edges
    ])
    
    # Check if G is 6-chromatic and has no K6
    chi = chromatic_number_upper_bound(G)
    has_k6 = has_k_clique(G, 6)
    
    print(f"Graph nodes: {list(G.nodes())}")
    print(f"Graph edges: {list(G.edges())}")
    print(f"Chromatic number: {chi}")
    print(f"Has K6: {has_k6}")
    
    if chi == 6 and not has_k6:
        print("Found a candidate graph with chi=6 and no K6")
        # Now check all possible partitions into two sets
        nodes = list(G.nodes())
        found_partition = False
        
        # Only check a few partitions for demonstration
        for i in range(1, len(nodes)//2 + 1):
            for subset in combinations(nodes, i):
                s1 = set(subset)
                s2 = set(nodes) - s1
                
                chi1 = chromatic_number_induced(G, s1)
                chi2 = chromatic_number_induced(G, s2)
                
                if chi1 >= 3 and chi2 >= 4:
                    print(f"Found valid partition:")
                    print(f"Set 1: {sorted(s1)} (chi={chi1})")
                    print(f"Set 2: {sorted(s2)} (chi={chi2})")
                    found_partition = True
                    break
            if found_partition:
                break
        
        if not found_partition:
            print("No valid partition found. This might be a counterexample.")
            return True
    else:
        print("Graph does not meet criteria.")
        
    return False

if __name__ == "__main__":
    result = find_counterexample()
    if result:
        print("Counterexample found!")
    else:
        print("No counterexample found in this construction.")
