extern crate bhtree;
use bhtree::*;

fn main() {
    // Sample points
    let body_data = vec![
        Point::Cartesian(0.4, 0.4, 0.4),
        Point::Cartesian(0.8, 0.8, 0.8),
        Point::Cartesian(-0.6, -0.6, -0.6),
    ];

    // Create the tree - mutable due to `insert`
    let mut tree = BHTree::new();

    // Insert bodies
    let mut bodies = body_data
        .iter()
        .map(|val| Body::new(*val, 100.0))
        .collect::<Vec<Body>>();

    for _ in 0..body_data.len() {
        tree.insert(bodies.remove(0));
    }

    // Display the tree
    println!("{}", tree.display(0));
}