#!/usr/bin/env python3
"""
Simulation of an averaging algorithm on directed communication graphs.

The algorithm starts with each node having an initial value x[0] in R^d.
In each iteration, each node receives values from other nodes according to
a directed communication graph and sets its new value to the average of
the received values.
"""

import os
from collections import defaultdict

import matplotlib
import matplotlib.colors as mcolors
import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
import plotly.graph_objects as go
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from numpy.typing import NDArray

# Set matplotlib to use PDF backend for better compatibility
matplotlib.use('PDF')

# Global cache for node positions to keep them consistent across plots
_node_positions_cache: dict[int, dict] = {}


class Graph:
    """Represents a directed communication graph."""
    
    def __init__(self, edges: list[tuple[int, int]], num_nodes: int) -> None:
        """
        Initialize a directed graph.
        
        Args:
            edges: List of directed edges (u, v) where u -> v
            num_nodes: Total number of nodes in the graph
        """
        self.edges: list[tuple[int, int]] = edges
        self.num_nodes: int = num_nodes
        self.adjacency: dict[int, list[int]] = defaultdict(list)
        
        for u, v in edges:
            self.adjacency[u].append(v)
    
    def get_neighbors(self, node: int) -> list[int]:
        """Get outgoing neighbors of a node."""
        return self.adjacency.get(node, [])
    
    def get_in_neighbors(self, node: int) -> list[int]:
        """Get incoming neighbors of a node."""
        in_neighbors: list[int] = []
        for u, neighbors in self.adjacency.items():
            if node in neighbors:
                in_neighbors.append(u)
        return in_neighbors



def run_averaging_algorithm(G: list[Graph], x0: list[NDArray[np.float64]], T: int) -> list[list[NDArray[np.float64]]]:
    """
    Run the averaging algorithm simulation.
    
    Args:
        G: List of directed communication graphs (one for each iteration)
        x0: List of initial values for each node (each value is in R^d)
        T: Number of iterations to run
        
    Returns:
        List of lists containing the state of each node at each time step
        x[t][i] gives the value of node i at time t
    """
    
    # Validate inputs
    if not G:
        raise ValueError("Graph list G cannot be empty")
    
    num_nodes = G[0].num_nodes
    d = len(x0[0]) if x0 else 0
    
    if len(x0) != num_nodes:
        raise ValueError(f"Number of initial values ({len(x0)}) must match number of nodes ({num_nodes})")
    
    # Initialize the state
    x = [x0.copy()]  # x[t][i] is the value of node i at time t
    
    T = min(T, len(G))  # Ensure we don't exceed the number of provided graphs
    for t in range(1, T + 1):
        # Get the graph for this time step (cycle through the provided graphs)
        current_graph = G[t-1]
        
        new_values = []
        
        for i in range(num_nodes):
            # Get incoming neighbors (nodes that send to i)
            in_neighbors = current_graph.get_in_neighbors(i)

            # Always include the node's own value in the average
            neighbor_values = [x[t-1][i]] + [x[t-1][j] for j in in_neighbors]
            new_value = np.mean(neighbor_values, axis=0)

            new_values.append(new_value)
        
        x.append(new_values)
    
    return x



def generate_initial_values(num_nodes: int, d: int = 3, seed: int = 42) -> list[NDArray[np.float64]]:
    """Generate initial values for nodes spread across the unit cube."""
    np.random.seed(seed)
    # Create values spread across the unit cube for better visualization
    values = []
    for i in range(num_nodes):
        # Use i to create a more structured spread
        val = np.array([(i % 2), ((i // 2) % 2), (i % 3) / 2.0], dtype=np.float64)
        # Add small random perturbation to avoid perfect symmetry
        val += np.random.rand(d) * 0.1
        values.append(np.clip(val, 0.1, 0.9))
    return values



def plane_cube_intersection(centroid: NDArray[np.float64], normal: NDArray[np.float64]) -> list[NDArray[np.float64]]:
    """
    Find intersection points of a plane with the unit cube [0,1]³.

    Args:
        centroid: A point on the plane
        normal: Normal vector to the plane

    Returns:
        List of intersection points ordered to form a polygon
    """
    points = []
    d = np.dot(normal, centroid)

    # Check intersection with 6 cube faces
    # Face x=0
    if abs(normal[0]) > 1e-10:
        t = (d - normal[1]*0 - normal[2]*0) / normal[0]
        # But we're looking for plane at x=0
        t = d / normal[0]
        y_range = np.linspace(0, 1, 100)
        z_range = np.linspace(0, 1, 100)
        for y in [0, 1]:
            for z in [0, 1]:
                # Check if this point is on the plane
                if abs(normal[0]*0 + normal[1]*y + normal[2]*z - d) < 0.1:
                    points.append(np.array([0, y, z]))

    # More systematic approach: check all edges and vertices of the cube
    vertices = []
    for x in [0, 1]:
        for y in [0, 1]:
            for z in [0, 1]:
                vertices.append(np.array([x, y, z]))

    # Find intersections with edges
    edges = [
        (0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)
    ]

    intersection_points = []
    for i, j in edges:
        p1 = vertices[i]
        p2 = vertices[j]
        # Check if plane intersects edge
        val1 = np.dot(normal, p1) - d
        val2 = np.dot(normal, p2) - d

        if val1 * val2 < 0:  # Sign change = intersection
            t = val1 / (val1 - val2)
            intersection_points.append(p1 + t * (p2 - p1))

    # Also check face intersections
    # For each face, find intersection polygon
    faces = [
        # x = 0
        (np.array([0, 0, 0]), np.array([0, 1, 0]), np.array([0, 1, 1]), np.array([0, 0, 1])),
        # x = 1
        (np.array([1, 0, 0]), np.array([1, 1, 0]), np.array([1, 1, 1]), np.array([1, 0, 1])),
        # y = 0
        (np.array([0, 0, 0]), np.array([1, 0, 0]), np.array([1, 0, 1]), np.array([0, 0, 1])),
        # y = 1
        (np.array([0, 1, 0]), np.array([1, 1, 0]), np.array([1, 1, 1]), np.array([0, 1, 1])),
        # z = 0
        (np.array([0, 0, 0]), np.array([1, 0, 0]), np.array([1, 1, 0]), np.array([0, 1, 0])),
        # z = 1
        (np.array([0, 0, 1]), np.array([1, 0, 1]), np.array([1, 1, 1]), np.array([0, 1, 1])),
    ]

    # Remove duplicates and sort by angle from centroid
    if intersection_points:
        intersection_points = [p for i, p in enumerate(intersection_points) if not any(np.allclose(p, intersection_points[j]) for j in range(i))]
        if len(intersection_points) >= 3:
            face_centroid = np.mean(intersection_points, axis=0)
            # Project to plane and sort by angle
            ref_vec = intersection_points[0] - face_centroid
            def angle_key(p):
                v = p - face_centroid
                return np.arctan2(np.dot(np.cross(ref_vec, v), normal), np.dot(ref_vec, v))
            intersection_points.sort(key=angle_key)
            return intersection_points

    return []


def create_circular_positions(num_nodes: int) -> dict:
    """
    Create positions for nodes arranged in a circle numbered 0, 1, 2, 3, ...

    Args:
        num_nodes: Number of nodes to arrange

    Returns:
        Dictionary mapping node index to (x, y) position on a circle
    """
    positions = {}
    for i in range(num_nodes):
        # Calculate angle: 0 at top, going clockwise
        angle = 2 * np.pi * i / num_nodes - np.pi / 2
        x = np.cos(angle)
        y = np.sin(angle)
        positions[i] = (x, y)
    return positions


def plot_graph(graph: Graph, name: str = "graph", broadcasters: set[int] | None = None) -> None:
    """
    Plot a graph and save it as a PDF file in the results directory.

    Node positions are cached from the first plot and reused for subsequent plots
    with the same number of nodes, ensuring consistency across visualizations.

    Args:
        graph: Graph object to plot
        name: Base name for the output file (default: "graph")
        broadcasters: Optional set of node indices to highlight in red

    Returns:
        None
    """
    global _node_positions_cache

    # Create results directory if it doesn't exist
    os.makedirs("results", exist_ok=True)

    # Create a networkx graph for visualization
    nx_graph = nx.DiGraph()
    nx_graph.add_edges_from(graph.edges)

    # Add all nodes explicitly to ensure isolated nodes are included
    for i in range(graph.num_nodes):
        if i not in nx_graph:
            nx_graph.add_node(i)

    # Create figure with smaller size for denser plot
    plt.figure(figsize=(1, 1))

    # Use cached positions if available, otherwise compute and cache
    num_nodes = graph.num_nodes
    if num_nodes not in _node_positions_cache:
        pos = create_circular_positions(num_nodes)
        _node_positions_cache[num_nodes] = pos
    else:
        pos = _node_positions_cache[num_nodes]

    # Create node colors list - red for broadcasters, steelblue for others
    # Must order by actual node order in graph, not by index
    if broadcasters is not None:
        node_colors = ['#ff6b6b' if node in broadcasters else 'steelblue' for node in nx_graph.nodes()]
    else:
        node_colors = 'steelblue'

    nx.draw(
        nx_graph, pos, with_labels=False,
        node_size=120, node_color=node_colors,
        arrowsize=10, width=1.5
    )

    xs = [p[0] for p in pos.values()]
    ys = [p[1] for p in pos.values()]
    pad = .2
    plt.xlim(min(xs) - pad, max(xs) + pad)
    plt.ylim(min(ys) - pad, max(ys) + pad)

    plt.axis("off")
    output_path_pdf = os.path.join("results", f"{name}.pdf")
    output_path_svg = os.path.join("results", f"{name}.svg")
    plt.savefig(output_path_pdf, format="pdf")
    plt.savefig(output_path_svg, format="svg")
    plt.close()

    print(f"Graph saved as PDF: {output_path_pdf}")
    print(f"Graph saved as SVG: {output_path_svg}")


def fit_plane_3d(points: NDArray[np.float64]) -> tuple:
    """
    Fit a plane through 3D points using PCA.

    Args:
        points: Array of shape (n, 3) containing 3D points

    Returns:
        Tuple of (centroid, normal_vector, [pc1, pc2]) where:
        - centroid: Center of the plane
        - normal_vector: Normal to the plane (smallest PC)
        - pc1, pc2: Two orthogonal vectors in the plane
    """
    # Compute centroid
    centroid = np.mean(points, axis=0)

    # Center the points
    centered = points - centroid

    # Compute SVD
    u, _, vh = np.linalg.svd(centered)

    # The first two components define the plane
    pc1 = vh[0]
    pc2 = vh[1]

    # Normal to the plane is the smallest component
    normal = vh[2]

    return centroid, normal, (pc1, pc2)


def calculate_plane_fit_r2(points: NDArray[np.float64], centroid: NDArray[np.float64],
                           normal: NDArray[np.float64]) -> float:
    """
    Calculate R² for fitting a plane to the data.

    Args:
        points: Array of shape (n, 3) containing 3D points
        centroid: Center of the fitted plane
        normal: Normal vector to the fitted plane

    Returns:
        R² value (0 to 1, higher is better)
    """
    # Residuals: perpendicular distances from points to plane
    residuals = []
    for point in points:
        v = point - centroid
        dist = abs(np.dot(v, normal))
        residuals.append(dist)

    residuals = np.array(residuals)
    ss_residual = np.sum(residuals ** 2)

    # Total sum of squares
    ss_total = np.sum((points - np.mean(points, axis=0)) ** 2)

    # Avoid division by zero
    if ss_total == 0:
        return 1.0

    r_squared = 1 - (ss_residual / ss_total)
    return r_squared


def fit_line_3d(points: NDArray[np.float64]) -> tuple[NDArray[np.float64], NDArray[np.float64]]:
    """
    Fit a 3D line through points using least squares (PCA).

    Args:
        points: Array of shape (n, 3) containing 3D points

    Returns:
        Tuple of (centroid, direction_vector)
    """
    # Compute centroid
    centroid = np.mean(points, axis=0)

    # Center the points
    centered = points - centroid

    # Compute SVD
    _, _, vh = np.linalg.svd(centered)

    # Direction is the first principal component
    direction = vh[0]

    return centroid, direction


def calculate_point_fit_r2(points: NDArray[np.float64]) -> float:
    """
    Calculate R² for fitting a point (centroid) to the data.
    Measures how tightly points cluster around their centroid.

    Args:
        points: Array of shape (n, 3) containing 3D points

    Returns:
        R² value (0 to 1, higher = tighter clustering around centroid)
    """
    centroid = np.mean(points, axis=0)

    # Calculate distances from points to centroid
    distances = np.linalg.norm(points - centroid, axis=1)
    mean_distance = np.mean(distances)

    # Maximum possible distance in [0,1]³ space (diagonal)
    max_distance = np.sqrt(3)

    # R² = 1 - (actual_spread / max_spread)
    # If all points at centroid: mean_distance=0, R²=1
    # If points spread across space: mean_distance→max_distance, R²→0
    r_squared = 1 - (mean_distance / max_distance)
    return r_squared


def calculate_line_fit_r2(points: NDArray[np.float64], centroid: NDArray[np.float64],
                          direction: NDArray[np.float64]) -> float:
    """
    Calculate R² for fitting a line to the data.

    Args:
        points: Array of shape (n, 3) containing 3D points
        centroid: Center of the fitted line
        direction: Direction vector of the fitted line

    Returns:
        R² value (0 to 1, higher is better)
    """
    # Residuals: perpendicular distances from points to line
    residuals = []
    for point in points:
        v = point - centroid
        proj_length = np.dot(v, direction)
        proj = proj_length * direction
        perp = v - proj
        dist = np.linalg.norm(perp)
        residuals.append(dist)

    residuals = np.array(residuals)
    ss_residual = np.sum(residuals ** 2)

    # Total sum of squares
    ss_total = np.sum((points - np.mean(points, axis=0)) ** 2)

    # Avoid division by zero
    if ss_total == 0:
        return 1.0

    r_squared = 1 - (ss_residual / ss_total)
    return r_squared


def lighten(color: str, amount: float) -> tuple:
    """
    Lighten a color by blending it with white.

    Args:
        color: Color name or hex code
        amount: Lightening amount from 0 (original) to 1 (white)

    Returns:
        RGB tuple
    """
    rgb = mcolors.to_rgb(color)
    return rgb



def plot_execution(x: list[list[NDArray[np.float64]]], name: str, highlight_nodes: tuple[int, int] | None = None) -> None:
    """
    Plot the execution of the averaging algorithm as 3D trajectories.

    Creates a 3D plot where each node's values over time are shown as a trajectory,
    with points connected to show the path taken by each node.

    Args:
        x: Output from run_averaging_algorithm, where x[t][i] is node i's value at time t
        name: Base name for the output file
        highlight_nodes: Optional tuple of two node indices (node1, node2) to draw a dashed line through

    Returns:
        None
    """
    # Create results directory if it doesn't exist
    os.makedirs("results", exist_ok=True)

    fig = plt.figure(figsize=(3, 3))
    ax = fig.add_subplot(111, projection='3d')

    base_color = 'steelblue'
    lightened_color = lighten(base_color, 0.5)

    num_nodes = len(x[0])

    # Plot trajectory for each node
    for node in range(num_nodes):
        # Extract coordinates for this node over all time steps
        trajectory = np.array([x[t][node] for t in range(len(x))])

        # Connect points with lines to show trajectory using same lightened color
        ax.plot(trajectory[:, 0], trajectory[:, 1], trajectory[:, 2],
               color=lightened_color, linewidth=1, alpha=0.5)

        # Add arrow on first edge where node actually moves with fixed length
        if len(trajectory) > 1:
            # Find first edge where node actually moves
            for i in range(len(trajectory) - 1):
                p1 = trajectory[i]
                p2 = trajectory[i + 1]
                direction = p2 - p1
                dist = np.linalg.norm(direction)
                if dist > 1e-10:  # Node actually moved
                    direction_norm = direction / dist
                    arrow_length = 0.2  # Fixed absolute arrow length
                    ax.quiver(p1[0], p1[1], p1[2],
                             arrow_length * direction_norm[0], arrow_length * direction_norm[1], arrow_length * direction_norm[2],
                             color=lightened_color, arrow_length_ratio=0.3,
                             alpha=1.0)
                    break  # Only draw one arrow

        # Plot initial point with color and larger size
        ax.scatter(trajectory[0, 0], trajectory[0, 1], trajectory[0, 2],
                  s=80, color=lightened_color, alpha=1.0)

        # Plot final point with black color and larger size
        ax.scatter(trajectory[-1, 0], trajectory[-1, 1], trajectory[-1, 2],
                  s=80, color='black', alpha=1.0)

    # Draw dashed line through two specified nodes if provided
    if highlight_nodes is not None:
        node1, node2 = highlight_nodes
        if 0 <= node1 < num_nodes and 0 <= node2 < num_nodes:
            # Get final positions of the two nodes
            p1 = np.array(x[-1][node1])
            p2 = np.array(x[-1][node2])

            # Calculate direction vector
            direction = p2 - p1

            # Extend the line in both directions
            t_range = np.linspace(-1, 2, 100)
            line_points = p1[np.newaxis, :] + direction[np.newaxis, :] * t_range[:, np.newaxis]

            # Plot dashed line
            ax.plot(line_points[:, 0], line_points[:, 1], line_points[:, 2],
                   color='#ff6b6b', linewidth=2, linestyle='--', alpha=0.8, zorder=5)

    # ax.set_xlabel('X')
    # ax.set_ylabel('Y')
    # ax.set_zlabel('Z')

    # Set axis limits and ticks for Nature paper style
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_zlim(0, 1)

    ax.set_xticks([0, 0.5, 1])
    ax.set_yticks([0, 0.5, 1])
    ax.set_zticks([0, 0.5, 1])
    ax.tick_params(axis='both', which='major', labelsize=12)

    # Remove grid lines
    ax.grid(False)

    # Find final converged points
    final_values = np.array(x[-1])

    # Cluster final values to find unique convergence points
    unique_values = []
    tolerance = 1e-3

    for val in final_values:
        is_new = True
        for u_val in unique_values:
            if np.linalg.norm(val - u_val) < tolerance:
                is_new = False
                break
        if is_new:
            unique_values.append(val)

    unique_values = np.array(unique_values)
    num_components = len(unique_values)

    # Analyze based on convergence type
    if name.endswith("k1"):
        # For k=1: calculate and print R² for point fit (how well nodes cluster to their centroid)
        r_squared = calculate_point_fit_r2(final_values)
        print(f"k=1 point fit: R² = {r_squared:.6f} ({r_squared*100:.2f}% variance explained)")

    elif name.endswith("k2"):
        # For k=2: fit a line through all final points
        centroid, direction = fit_line_3d(final_values)

        # Create line endpoints for visualization
        t_range = np.linspace(-0.5, 0.5, 100)
        line_points = centroid[np.newaxis, :] + direction[np.newaxis, :] * t_range[:, np.newaxis]

        # Plot the fitted line
        ax.plot(line_points[:, 0], line_points[:, 1], line_points[:, 2],
               color='black', linewidth=2, zorder=10)

        # Calculate and print R² for line fit
        r_squared = calculate_line_fit_r2(final_values, centroid, direction)
        print(f"k=2 line fit: R² = {r_squared:.6f} ({r_squared*100:.2f}% variance explained)")

    elif name.endswith("k3"):
        # For k=3: fit a plane through all final points
        centroid, normal, (pc1, pc2) = fit_plane_3d(final_values)

        # Find plane-cube intersection polygon
        intersection_pts = plane_cube_intersection(centroid, normal)
        if len(intersection_pts) >= 3:
            vertices = [intersection_pts]
            poly = Poly3DCollection(vertices, alpha=0.3, facecolor='grey', edgecolor='none')
            ax.add_collection3d(poly)

        # Calculate and print R² for plane fit
        r_squared = calculate_plane_fit_r2(final_values, centroid, normal)
        print(f"k=3 plane fit: R² = {r_squared:.6f} ({r_squared*100:.2f}% variance explained)")

    else:
        # For k=1 if not converged to single point
        print(f"k=1: Converged to {num_components} distinct points")

    # Add padding to avoid cutting off labels
    plt.subplots_adjust(left=0.1, right=0.85, top=1.1, bottom=0)

    output_path_pdf = os.path.join("results", f"{name}_execution.pdf")
    output_path_svg = os.path.join("results", f"{name}_execution.svg")
    plt.savefig(output_path_pdf, format="pdf")
    plt.savefig(output_path_svg, format="svg")
    plt.close()

    print(f"Execution plot saved as PDF: {output_path_pdf}")

    # Create interactive HTML plot
    plot_execution_interactive(x, name)


def plot_execution_interactive(x: list[list[NDArray[np.float64]]], name: str) -> None:
    """
    Create an interactive 3D plot using plotly.

    Args:
        x: Output from run_averaging_algorithm
        name: Base name for the output file
    """
    os.makedirs("results", exist_ok=True)

    fig = go.Figure()

    num_nodes = len(x[0])
    colors = ['steelblue', 'red', 'green', 'orange', 'purple', 'brown', 'pink', 'gray', 'olive', 'cyan']

    # Add trajectories for each node
    for node in range(num_nodes):
        trajectory = np.array([x[t][node] for t in range(len(x))])
        color = colors[node % len(colors)]

        # Add trajectory line
        fig.add_trace(go.Scatter3d(
            x=trajectory[:, 0], y=trajectory[:, 1], z=trajectory[:, 2],
            mode='lines',
            line=dict(color=color, width=2),
            name=f'Node {node} path',
            hoverinfo='skip'
        ))


        # Add initial point
        fig.add_trace(go.Scatter3d(
            x=[trajectory[0, 0]], y=[trajectory[0, 1]], z=[trajectory[0, 2]],
            mode='markers',
            marker=dict(size=8, color=color),
            name=f'Node {node} initial',
            hovertext=f'Node {node} initial: [{trajectory[0, 0]:.3f}, {trajectory[0, 1]:.3f}, {trajectory[0, 2]:.3f}]'
        ))

        # Add final point (black)
        fig.add_trace(go.Scatter3d(
            x=[trajectory[-1, 0]], y=[trajectory[-1, 1]], z=[trajectory[-1, 2]],
            mode='markers',
            marker=dict(size=8, color='black'),
            name=f'Node {node} final',
            hovertext=f'Node {node} final: [{trajectory[-1, 0]:.3f}, {trajectory[-1, 1]:.3f}, {trajectory[-1, 2]:.3f}]'
        ))

    # Get final values
    final_values = np.array(x[-1])

    # Add geometric structures
    if name.endswith("k2"):
        centroid, direction = fit_line_3d(final_values)
        t_range = np.linspace(-0.5, 0.5, 100)
        line_points = centroid[np.newaxis, :] + direction[np.newaxis, :] * t_range[:, np.newaxis]

        fig.add_trace(go.Scatter3d(
            x=line_points[:, 0], y=line_points[:, 1], z=line_points[:, 2],
            mode='lines',
            line=dict(color='black', width=3),
            name='Fitted line',
            hoverinfo='skip'
        ))

    elif name.endswith("k3"):
        centroid, normal, (pc1, pc2) = fit_plane_3d(final_values)

        # Find plane-cube intersection polygon
        intersection_pts = plane_cube_intersection(centroid, normal)
        if len(intersection_pts) >= 3:
            # Create triangles from the polygon using fan triangulation
            poly_array = np.array(intersection_pts)
            n = len(poly_array)
            i_idx = [0] * (n - 2)  # All triangles share vertex 0
            j_idx = list(range(1, n - 1))
            k_idx = list(range(2, n))

            fig.add_trace(go.Mesh3d(
                x=poly_array[:, 0],
                y=poly_array[:, 1],
                z=poly_array[:, 2],
                i=i_idx,
                j=j_idx,
                k=k_idx,
                opacity=0.3,
                color='grey',
                name='Fitted plane',
                hoverinfo='skip',
                showlegend=True
            ))

    # Update layout
    fig.update_layout(
        scene=dict(
            xaxis=dict(range=[0, 1]),
            yaxis=dict(range=[0, 1]),
            zaxis=dict(range=[0, 1]),
            camera=dict(eye=dict(x=1.5, y=1.5, z=1.3))
        ),
        title=f'Interactive: {name}',
        hovermode='closest',
        width=900,
        height=900
    )

    output_path = os.path.join("results", f"{name}_execution.html")
    fig.write_html(output_path)
    print(f"Interactive HTML plot saved: {output_path}")


def create_k_forest_graph(num_nodes: int, k: int, seed: int = 42) -> Graph:
    """
    Create a directed graph with exactly k roots (k-forest).

    A k-forest is a graph with k connected components, each forming a random tree
    with edges pointing toward the root.

    Note: When num_nodes >= 2*k, each component will have at least 2 nodes.
    When num_nodes < 2*k, some components will have only 1 node (isolated roots).

    Args:
        num_nodes: Total number of nodes in the graph
        k: Number of roots (connected components)
        seed: Random seed for reproducibility (default: 42)

    Returns:
        Graph with exactly k roots

    Raises:
        ValueError: If k <= 0 or k > num_nodes
    """
    if k <= 0:
        raise ValueError("k must be positive")
    if k > num_nodes:
        raise ValueError("k cannot be greater than num_nodes")

    np.random.seed(seed)

    # Distribute nodes across components
    # Give each component at least num_nodes // k nodes
    base_nodes = num_nodes // k
    extra_nodes = num_nodes % k

    nodes_per_component = [base_nodes] * k
    # Distribute the extra nodes randomly
    extra_indices = np.random.choice(k, extra_nodes, replace=False)
    for idx in extra_indices:
        nodes_per_component[idx] += 1

    # Assign nodes to components
    component_assignments = []
    node_idx = 0
    for component in range(k):
        for _ in range(nodes_per_component[component]):
            component_assignments.append(component)
            node_idx += 1

    # Shuffle to randomize which nodes go to which component
    np.random.shuffle(component_assignments)

    edges = []

    # For each component, create a random tree
    for component in range(k):
        # Find all nodes in this component
        component_nodes = [i for i, comp in enumerate(component_assignments) if comp == component]

        if len(component_nodes) <= 1:
            # Single node component (isolated root)
            continue

        # Randomize the order to randomize which node is root
        np.random.shuffle(component_nodes)

        # For each non-root node, create an edge to a random parent already in tree
        # This creates a random tree structure
        for idx, node in enumerate(component_nodes[1:], start=1):
            # Parent can be any node already processed (including root)
            parent = component_nodes[np.random.randint(0, idx)]
            edges.append((parent, node))

    return Graph(edges, num_nodes)



def plot_broadcaster_angles(vectors_over_time: list[list[NDArray[np.float64]]]) -> None:
    """
    Plot the angles of broadcaster projection lines over time.

    Each line is represented by two spherical angles (theta, phi).
    Since x and -x represent the same projection, angles are normalized to [0, π).

    Args:
        vectors_over_time: List of lists where vectors_over_time[t] contains vectors at time t
    """
    # Compute angles for all vectors
    theta_values = []  # Azimuthal angle
    phi_values = []    # Polar angle
    time_indices = []

    for t, vectors_at_t in enumerate(vectors_over_time):
        for v_vec in vectors_at_t:
            v_length = np.linalg.norm(v_vec)
            if v_length < 1e-10:
                continue

            v_normalized = v_vec / v_length

            # Compute spherical coordinates
            x, y, z = v_normalized

            # Azimuthal angle (theta): arctan2(y, x)
            theta = np.arctan2(y, x)

            # Polar angle (phi): arccos(z / |v|) = arccos(z) since normalized
            phi = np.arccos(np.clip(z, -1, 1))

            # Normalize angles to handle equivalence of v and -v
            # For projection lines, angles differing by π are equivalent
            # Map to [0, π) range for theta and [0, π/2] for phi
            if theta < 0:
                theta += np.pi

            time_indices.append(t)
            theta_values.append(theta)
            phi_values.append(phi)

    # Create figure with single y-axis
    fig, ax = plt.subplots(figsize=(4, 2))

    # Plot theta angles
    ax.scatter(time_indices, np.degrees(theta_values), s=20, color='#83dc79', label='θ')
    ax.plot(time_indices, np.degrees(theta_values), linewidth=0.5, color='#83dc79')
    # Plot phi angles
    ax.scatter(time_indices, np.degrees(phi_values), s=20, color='darkorange', label='φ')
    ax.plot(time_indices, np.degrees(phi_values), linewidth=0.5, color='darkorange')

    ax.set_xlabel('Round', fontsize=14)
    ax.set_ylabel('Angle (degrees)', fontsize=14)
    ax.set_ylim(-10, 190)
    ax.set_yticks([0, 90, 180])
    ax.tick_params(axis='both', which='major', labelsize=12)

    # Legend without box, positioned outside right
    ax.legend(loc='upper left', bbox_to_anchor=(1, 1), fontsize=14, frameon=False)

    # Remove grid and spines
    ax.grid(False)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)

    plt.tight_layout()

    os.makedirs("results", exist_ok=True)
    output_path = os.path.join("results", "broadcaster_angles.pdf")
    plt.savefig(output_path, format="pdf", bbox_inches='tight', dpi=150)
    plt.savefig(output_path.replace('.pdf', '.svg'), format="svg", bbox_inches='tight')
    plt.close()

    print(f"Angles plot saved: {output_path}")


def animate_execution(x: list[list[NDArray[np.float64]]], name: str = "execution") -> None:
    """
    Create an animation of the node value trajectories over time.

    Args:
        x: Simulation states from run_averaging_algorithm
        name: Base name for the output file
    """
    from matplotlib.animation import FuncAnimation, FFMpegWriter

    num_nodes = len(x[0])
    T = len(x)

    fig = plt.figure(figsize=(6, 6))
    ax = fig.add_subplot(111, projection='3d')

    # Pre-compute all trajectories
    trajectories = [[x[t][i] for t in range(T)] for i in range(num_nodes)]

    def update(frame):
        ax.clear()

        # Plot trajectories up to current frame
        for i, traj in enumerate(trajectories):
            traj_up_to_frame = traj[:frame + 1]
            if len(traj_up_to_frame) > 0:
                traj_array = np.array(traj_up_to_frame)
                ax.plot(traj_array[:, 0], traj_array[:, 1], traj_array[:, 2],
                       alpha=0.6, linewidth=2)
                # Plot current point
                ax.scatter(traj_array[-1, 0], traj_array[-1, 1], traj_array[-1, 2],
                          s=100, alpha=0.8)

        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.set_zlim(0, 1)
        ax.set_xlabel('x')
        ax.set_ylabel('y')
        ax.set_zlabel('z')
        ax.set_title(f't = {frame}')

    anim = FuncAnimation(fig, update, frames=T, interval=1000, repeat=True)

    os.makedirs("results", exist_ok=True)
    output_path = os.path.join("results", f"{name}_animation.mp4")

    writer = FFMpegWriter(fps=5, metadata=dict(artist=''), bitrate=1800)
    anim.save(output_path, writer=writer)
    plt.close()

    print(f"Execution animation saved: {output_path}")


def main():
    """Main function to run the simulation and generate figures."""

    print("Running averaging algorithm simulation...")
    
    # Parameters
    num_nodes = 5
    d = 3
    T = 20
    
    # Generate sample graphs
    graphs = {k: [] for k in [1, 2, 3]}
    for k in [1, 2, 3]:
        print(f"\nCreating k-forest graph with k={k}...")
        for i in range(3):  # Create 3 different graphs for each k
            k_forest = create_k_forest_graph(num_nodes, k, seed=42+i)
            
            # Plot the graph
            plot_graph(k_forest, f"k_forest_k{k}_nr{i}")

            # Store the graph
            graphs[k] += [ k_forest ]

    
    # Generate initial values
    x0 = generate_initial_values(num_nodes, d)
    
    print(f"Initial values:")
    for i, val in enumerate(x0):
        print(f"  Node {i}: {val}")
    
    # Run the algorithm and plot execution
    for k in [1, 2, 3]:
        print(f"\nRunning algorithm for k={k}...")
        graph_sequence = []

        if k == 1:
            for cycle in range(10):
                graph_sequence.append(graphs[k][cycle % 3])

        elif k == 2:
            for cycle in range(2):
                graph_sequence.append(graphs[k][cycle % 3])
            for cycle in range(7):
                graph_sequence.append(graphs[k][1])
            for cycle in range(1):
                graph_sequence.append(graphs[k][2])
            # for cycle in range(2):
            #     graph_sequence.append(graphs[k][2])

        else:
            for cycle in range(3):
                graph_sequence.append(graphs[k][cycle % 3])
            graph_sequence.append(graphs[k][1])
            graph_sequence.append(graphs[k][2])
            graph_sequence.append(graphs[k][2])
            graph_sequence.append(graphs[k][2])
            graph_sequence.append(graphs[k][2])
            graph_sequence.append(graphs[k][2])
            graph_sequence.append(graphs[k][1])
            # graph_sequence.append(graphs[k][1])
            # graph_sequence.append(graphs[k][1])
        
        x = run_averaging_algorithm(graph_sequence, x0, T)
        print(f"Simulation length: {len(graph_sequence)} rounds")
        plot_execution(x, f"k_forest_k{k}")
        animate_execution(x, f"k_forest_k{k}")

    # Generate visualizations for custom sequence
    print("\nGenerating visualizations for custom sequence...")
    G1 = Graph([(0, 1), (2, 3), (2, 4)], 5)
    G2 = Graph([(0, 1), (0, 3), (2, 4)], 5)
    G3 = Graph([(3, 1), (3, 0), (4, 2)], 5)

    # Define broadcasters for each graph
    broadcasters_G1 = {0, 2}
    broadcasters_G2 = {0, 2}
    broadcasters_G3 = {4, 3}

    print(f"G1 broadcasters: {broadcasters_G1}")
    print(f"G2 broadcasters: {broadcasters_G2}")
    print(f"G3 broadcasters: {broadcasters_G3}")

    # Plot the graphs with broadcasting nodes highlighted
    plot_graph(G1, "graph_simple_0", broadcasters=broadcasters_G1)
    plot_graph(G2, "graph_simple_1", broadcasters=broadcasters_G2)
    plot_graph(G3, "graph_simple_2", broadcasters=broadcasters_G3)

    # Build custom sequence with all three graphs
    n = G1.num_nodes
    x0_custom = generate_initial_values(n, d=3, seed=42)

    # swap i,j in x0
    i, j = 0, 2
    x0_custom[i], x0_custom[j] = x0_custom[j], x0_custom[i]

    graph_sequence = []
    broadcaster_pairs = []
    for _ in range(3):  # 2 cycles
        for _ in range(1):
            graph_sequence.append(G1)
            broadcaster_pairs.append(broadcasters_G1)
        for _ in range(1):
            graph_sequence.append(G2)
            broadcaster_pairs.append(broadcasters_G2)
        for _ in range(2):
            graph_sequence.append(G3)
            broadcaster_pairs.append(broadcasters_G3)
    for _ in range(3):
        for _ in range(3):
            graph_sequence.append(G1)
            broadcaster_pairs.append(broadcasters_G1)
        for _ in range(3):
            graph_sequence.append(G2)
            broadcaster_pairs.append(broadcasters_G2)

    graph_sequence = graph_sequence
    broadcaster_pairs = broadcaster_pairs

    # Run algorithm
    x_custom = run_averaging_algorithm(graph_sequence, x0_custom, len(graph_sequence))

    # Compute difference vectors between broadcasters
    broadcaster_vectors = []
    for t in range(len(x_custom)):
        if t < len(broadcaster_pairs):
            b1, b2 = sorted(broadcaster_pairs[t])
        else:
            b1, b2 = sorted(broadcaster_pairs[-1])
        diff_vec = x_custom[t][b2] - x_custom[t][b1]
        broadcaster_vectors.append(diff_vec)
    # Plot execution
    print(f"Simulation length: {len(graph_sequence)} rounds")
    # Get broadcasting nodes from the last graph in the sequence
    last_broadcaster_pair = tuple(sorted(broadcaster_pairs[-1]))
    plot_execution(x_custom, "execution_simple", highlight_nodes=last_broadcaster_pair)
    animate_execution(x_custom, "execution_simple")

    # Plot execution prefixes up to round 10
    max_round = min(10, len(x_custom) - 1)
    for round_num in range(max_round + 1):
        # Extract execution data up to this round (inclusive)
        x_prefix = x_custom[:round_num + 1]

        # Get broadcasting nodes for this round
        if round_num < len(broadcaster_pairs):
            broadcaster_pair = tuple(sorted(broadcaster_pairs[round_num]))
        else:
            broadcaster_pair = tuple(sorted(broadcaster_pairs[-1]))

        # Create plot with the prefix data
        plot_name = f"execution_simple_{round_num}"
        plot_execution(x_prefix, plot_name, highlight_nodes=broadcaster_pair)

    # Normalize broadcaster vectors for plotting (limited to round 10)
    max_plot_round = min(10, len(broadcaster_vectors) - 1)
    vectors_normalized = [v/np.linalg.norm(v) if np.linalg.norm(v) > 1e-10 else v for v in broadcaster_vectors[:max_plot_round + 1]]
    # Wrap in list format for plotting functions
    vectors_for_plotting = [[v] for v in vectors_normalized]

    plot_broadcaster_angles(vectors_for_plotting)


if __name__ == "__main__":
    main()