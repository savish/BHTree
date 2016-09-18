# Barnes-Hut Algorithm

[![build status](https://gitlab.com/savish/bhtree/badges/master/build.svg)](https://gitlab.com/savish/bhtree/commits/master)

A Rust implementation of the Barnes-Hut tree in 3 dimensions.

This implementation focuses on the use of Rusts's enumerations to describe
multiple coordniate systems, as well as the tree structure that forms the heart
of the algorithm.

# Description

A detailed discussion on the Barnes-Hut algorithm is given [here][1].

## Implementation details

The main components of this implementation are:

- `Point <enum>`
- `Bounds <struct>`
- `Body <struct>`
- `BHTree <enum>`

There are 3 available coordinate systems to choose from:

- `Cartesian` : `x`, `y`, `z`
- `Cylindrical` : `r`, `phi`, `z`
- `Spherical` : `rho`, `phi`, `theta`

These are determined at the `Point` level (as variants of the enumeration), and,
for the most part, cannot be interchanged. The chosen system is used to describe
the limits of the `Bounds` instances and the centre of mass of the `Body`
instances and tree nodes.

Based on the algorithm, the `BHTree` enumeration has 3 variants:

- `Empty` : a tree node with no constituent `Body` instances
- `Node` : a tree node with exactly one consitient `Body` instance
- `Nodes` : a tree node with child nodes


[1]: http://arborjs.org/docs/barnes-hut