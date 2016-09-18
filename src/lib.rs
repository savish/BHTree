//! Barnes Hut Tree library
use std::ops::{Add, Sub};
use std::fmt;

use Point::{Cartesian, Cylindrical, Spherical};
use BHTree::{Empty, Node, Nodes};

const MATH_PI: f64 = std::f64::consts::PI;


fn subdivide_line(lower: f64, upper: f64) -> f64 {
    lower + ((upper - lower) / 2.0)
}

/// Defines a three-dimensional coordinate in space.
///
/// Two dimensional variants can be achieved by setting the value of the `z`
/// axis to zero for the `Cartesian` and `Cylindrical` coordinate systems.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Point {
    /// Point in cartesian space, described with:
    ///
    /// - `x` Distance along the x-axis
    /// - `y` Distance along the y-axis
    /// - `z` Distance along the z-axis
    Cartesian(f64, f64, f64),
    /// Point in cylindrical space, described with:
    ///
    /// - `r`   Distance form the origin to the projection of the point on the
    ///         azimuthal plane
    /// - `phi` Angle to the projection of the point on the azimuthal plane
    /// - `z`   Displacement of the point from the azimuthal plane
    Cylindrical(f64, f64, f64),
    /// Point in cartesian space, described with:
    ///
    /// - `rho`     Distance to the point from the origin
    /// - `phi`     Angle to the projection of the point on the azimuthal plane
    /// - `theta`   Polar angle to the point
    Spherical(f64, f64, f64),
}

impl Point {
    /// Returns a new `Point::Cartesian` variant, at (0, 0, 0)
    pub fn new() -> Point { Cartesian(0.0, 0.0, 0.0) }

    pub fn create(point: &Point, dim0: f64, dim1: f64, dim2: f64) -> Point {
        match *point {
            Cartesian(..) => Cartesian(dim0, dim1, dim2),
            Cylindrical(..) => Cylindrical(dim0, dim1, dim2),
            Spherical(..) => Spherical(dim0, dim1, dim2),
        }
    }

    /// Returns the lower point of the unit volume whose origin is the provided
    /// parameter.
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let lowerPoint = Point::lower(&Point::new());
    /// assert_eq!(lowerPoint, Point::Cartesian(-1.0, -1.0, -1.0));
    /// ```
    pub fn lower(point: &Point) -> Point {
        match *point {
            Cartesian(x, y, z) =>
                Cartesian(x - 1f64, y - 1f64, z - 1f64),
            Cylindrical(r, phi, z) =>
                Cylindrical(r, phi - MATH_PI, z - 1f64),
            Spherical(rho, phi, theta) =>
                Spherical(rho, phi - MATH_PI, theta),
        }
    }

    /// Returns the upper point of the unit volume whose origin is the provided
    /// parameter.
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let upperPoint = Point::upper(&Point::new());
    /// assert_eq!(upperPoint, Point::Cartesian(1.0, 1.0, 1.0));
    /// ```
    pub fn upper(point: &Point) -> Point {
        match *point {
            Cartesian(x, y, z) =>
                Cartesian(x + 1f64, y + 1f64, z + 1f64),
            Cylindrical(r, phi, z) =>
                Cylindrical(r + 1f64, phi + MATH_PI, z + 1f64),
            Spherical(rho, phi, theta) =>
                Spherical(rho + 1f64, phi + MATH_PI, theta + MATH_PI),
        }
    }

    /// Returns the value of a specified point dimension.
    ///
    /// # Arguments
    ///
    /// - `index` Dimension index (from 0)
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let p = Point::new();
    /// assert_eq!(p.dim(0), 0.0);
    /// ```
    pub fn dim(&self, index: i32) -> f64 {
        match *self {
            Cartesian(dim0, dim1, dim2) => {
                match index {
                    0 => dim0,
                    1 => dim1,
                    2 => dim2,
                    _ => 0.0,
                }
            },
            Cylindrical(dim0, dim1, dim2) => {
                match index {
                    0 => dim0,
                    1 => dim1,
                    2 => dim2,
                    _ => 0.0,
                }
            },
            Spherical(dim0, dim1, dim2) => {
                match index {
                    0 => dim0,
                    1 => dim1,
                    2 => dim2,
                    _ => 0.0,
                }
            }
        }
    }
}

impl Add for Point {
    type Output = Point;

    fn add(self, other: Point) -> Point {
        match self {
            Cartesian(x, y, z) => {
                if let Cartesian(_x, _y, _z) = other {
                    Cartesian(x + _x, y + _y, z + _z)
                } else {
                    panic!("Addition is only allowed between points in the same coordinate system");
                }
            },
            Cylindrical(r, phi, z) => {
                if let Cylindrical(_r, _phi, _z) = other {
                    Cylindrical(r + _r, phi + _phi, z + _z)
                } else {
                    panic!("Addition is only allowed between points in the same coordinate system");
                }
            },
            Spherical(rho, phi, theta) => {
                if let Spherical(_rho, _phi, _theta) = other {
                    Spherical(rho + _rho, phi + _phi, theta + _theta)
                } else {
                    panic!("Addition is only allowed between points in the same coordinate system");
                }
            },
        }
    }
}

impl Sub for Point {
    type Output = Point;

    fn sub(self, other: Point) -> Point {
        match self {
            Cartesian(x, y, z) => {
                if let Cartesian(_x, _y, _z) = other {
                    Cartesian(x - _x, y - _y, z - _z)
                } else {
                    panic!("Addition is only allowed between points in the same coordinate system");
                }
            },
            Cylindrical(r, phi, z) => {
                if let Cylindrical(_r, _phi, _z) = other {
                    Cylindrical(r - _r, phi - _phi, z - _z)
                } else {
                    panic!("Addition is only allowed between points in the same coordinate system");
                }
            },
            Spherical(rho, phi, theta) => {
                if let Spherical(_rho, _phi, _theta) = other {
                    Spherical(rho - _rho, phi - _phi, theta - _theta)
                } else {
                    panic!("Addition is only allowed between points in the same coordinate system");
                }
            },
        }
    }
}

impl fmt::Display for Point {
    // Displays the `Point` instance as a string. The output is limited to 2
    // decimal places by default. For example: `[2.45, 3.64]`
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Cartesian(x, y, z) =>
                write!(f, "[{:.2}, {:.2}, {:.2}]", x, y, z),
            Cylindrical(r, phi, z) =>
                write!(f, "[{:.2}, {:.2}, {:.2}]", r, phi, z),
            Spherical(rho, phi, theta) =>
                write!(f, "[{:.2}, {:.2}, {:.2}]", rho, phi, theta),
        }
    }
}



/// Defines the boundary points of a 3D volume
///
/// Irrespective of the coordinate system, a boundary volume can be defined by
/// using the lower limits of each coorindate as the `lower` point, and the
/// upper limits as the `upper` boundary point.
///
/// # Examples
///
/// ```
/// use bhtree::*;
///
/// let b = Bounds {
///     lower: Point::Cartesian(0.0, 0.0, 0.0),
///     upper: Point::Cartesian(1.0, 1.0, 1.0),
/// };
/// assert_eq!(b.lower, Point::Cartesian(0f64, 0f64, 0f64));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Bounds {
    /// A point containing the lower limit for each coordinate
    pub lower: Point,
    /// A point containing the upper limit for each coordinate
    pub upper: Point,
}

impl Bounds {
    /// Return a new `Bounds` object with an equivalent 'unit-like' volume.
    ///
    /// The `point` argument is used to determine the coordinate system for the
    /// `lower` and `upper` points of the volume.
    ///
    /// # Arguments
    ///
    /// - `point` The centre of the resulting volume.
    ///
    /// # Examples
    /// ```
    /// use bhtree::*;
    ///
    /// // This results in a `Bounds` instance whose coorindates will be
    /// // `Point::Cartesian` variants, at (-1, -1, -1) and (1, 1, 1).
    /// let b = Bounds::new(&Point::new());
    /// ```
    pub fn new(point: &Point) -> Bounds {
        Bounds {
            lower: Point::lower(point),
            upper: Point::upper(point),
        }
    }

    /// Returns the range between the upper and lower boundary points
    ///
    /// The range is represented as a `Point` whose values correspond to the
    /// range of allowable values for the specific axis.
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let b = Bounds::new(&Point::new());  // (-1, -1, -1) to (1, 1, 1)
    /// assert_eq!(b.range(), Point::Cartesian(2.0, 2f64, 2.0));
    /// ```
    pub fn range(&self) -> Point {
        self.upper - self.lower
    }

    /// Returns half of the range between the upper and lower boundary points
    ///
    /// The half-range is represented as a `Point` whose values correspond to
    /// half the range of allowable values for the specific axis.
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let b = Bounds::new(&Point::new());  // (-1, -1, -1) to (1, 1, 1)
    /// assert_eq!(b.half_range(), Point::Cartesian(1.0, 1f64, 1.0));
    /// ```
    pub fn half_range(&self) -> Point {
        let r = self.range();

        Point::create(
            &self.upper,
            r.dim(0) / 2f64,
            r.dim(1) / 2f64,
            r.dim(2) / 2f64,
        )
    }

    /// Returns the central point of the bounds instance
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let b = Bounds::new(&Point::new());
    /// assert_eq!(b.central_point().dim(0), 0f64);
    /// assert_eq!(b.central_point().dim(1), 0f64);
    /// assert_eq!(b.central_point().dim(2), 0f64);
    /// ```
    pub fn central_point(&self) -> Point {
        Point::create(
            &self.upper,
            subdivide_line(self.lower.dim(0), self.upper.dim(0)),
            subdivide_line(self.lower.dim(1), self.upper.dim(1)),
            subdivide_line(self.lower.dim(2), self.upper.dim(2)),
        )
    }

    /// Subdivide a volume into constituent volumes, halved along each axis.
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let b = Bounds::new(&Point::new());
    /// let b_sub = b.subdivide();
    /// assert_eq!(b_sub.len(), 8);
    /// assert_eq!(b_sub[0].upper, Point::Cartesian(0.0, 0.0, 0.0));
    /// ```
    pub fn subdivide(&self) -> Vec<Bounds> {
        let halfway_range = self.half_range();
        let halfway_point = self.central_point();

        let mut dim_values = Vec::new();
        for v in 0..3 {
            dim_values.push(vec![self.lower.dim(v), halfway_point.dim(v)])
        };


        let mut new_bounds = Vec::new();
        for dim0 in &dim_values[0] {
            for dim1 in &dim_values[1] {
                for dim2 in &dim_values[2] {
                    new_bounds.push(Bounds {
                        lower: Point::create(&self.upper, *dim0, *dim1, *dim2),
                        upper: Point::create(
                            &self.upper,
                            *dim0 + halfway_range.dim(0),
                            *dim1 + halfway_range.dim(1),
                            *dim2 + halfway_range.dim(2)
                        )
                    })
                }
            }
        }

        new_bounds
    }

    /// Determine if a point exists within a given volume.
    ///
    /// Bottom-left (lower) values are *included* whereas upper values are not.
    ///
    /// # Examples
    ///
    /// ```
    /// use bhtree::*;
    ///
    /// let p = Point::new();       // (0, 0, 0)
    /// let b = Bounds::new(&p);    // (-1, -1, -1) -> (1, 1, 1)
    /// assert_eq!(b.contains(&p), true);
    /// ```
    pub fn contains(&self, point: &Point) -> bool {
        for x in 0..3 {
            let contains = self.upper.dim(x) > point.dim(x) &&
                self.lower.dim(x) <= point.dim(x);

            if !contains { return contains }
        }
        true
    }
}


/// Defines a body that can be added to the BH tree
///
/// # Examples
///
/// ```
/// use bhtree::*;
///
/// let b = Body { centre: Point::Cartesian(0f64, 0f64, 0f64), mass: 10f64 };
/// assert_eq!(b.mass, 10.0);
/// assert_eq!(b.centre, Point::Cartesian(0.0, 0.0, 0.0));
/// ```
#[derive(Debug, Copy, Clone)]
pub struct Body {
    /// Centre of mass of the body
    pub centre: Point,
    /// Mass of the body
    pub mass: f64,
}

impl Body {
    pub fn new(centre: Point, mass: f64) -> Body {
        Body {
            mass: mass,
            centre: centre,
        }
    }

    /// Returns a new body that is the 'sum' of this one and the provided one.
    /// Specifically the noew body parmeters are:
    ///
    /// - `mass` Sum of the masses of the two bodies
    /// - `centre` Centre of mass of the two bodies
    fn combine(&self, other: &Body) -> Body {
        let _mass = self.mass + other.mass;
        Body {
            mass: _mass,
            centre: match self.centre {
                Cartesian(x, y, z) => {
                    if let Cartesian(o_x, o_y, o_z) = other.centre {
                        Cartesian(
                            ((x * self.mass) + (o_x * other.mass)) / _mass,
                            ((y * self.mass) + (o_y * other.mass)) / _mass,
                            ((z * self.mass) + (o_z * other.mass)) / _mass
                        )
                    } else {
                        other.centre
                    }
                },
                _ => other.centre,
            },
        }
    }
}

impl fmt::Display for Body {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Mass: {:.2}, Centre: {}", self.mass, self.centre)
    }
}


/// Defines a barnes-hut tree.
///
/// This data structure has a recursive variant (`Nodes`).
#[derive(Debug)]
pub enum BHTree {
    /// An empty tree node
    Empty(Bounds),
    /// A tree node with a single body
    Node(Bounds, Body),
    /// A tree node with child nodes
    Nodes(Bounds, Body, Vec<Box<BHTree>>),
}

impl BHTree {
    pub fn new() -> BHTree {
        BHTree::Empty(Bounds::new(&Point::new()))
    }

    pub fn insert(&mut self, body: Body) {
        match self {
            &mut Empty(bounds) => {
                if bounds.contains(&body.centre) {
                    *self = Node(bounds, body)
                }
            },
            &mut Node(bounds, self_body) => {
                if bounds.contains(&body.centre) {
                    let mut children = Vec::new();

                    for bounds in bounds.subdivide() {
                        let mut child = Empty(bounds);
                        child.insert(body);
                        child.insert(self_body);
                        children.push(Box::new(child));
                    };

                    *self = Nodes(bounds, self_body.combine(&body), children)
                }
            },
            &mut Nodes(bounds, ref mut self_body, ref mut children) => {
                if bounds.contains(&body.centre) {
                    for child in children {
                        child.insert(body)
                    }

                    *self_body = self_body.combine(&body);
                }
            },
        }
    }

    /// Returns a formatted string display of the tree
    pub fn display(&self, level: i32) -> String {
        let mut tree = String::new();
        match *self {
            Empty(_) => {
                tree = tree + format!("{}\n", "Empty").as_str();
                tree
            },
            Node(_, body) => {
                tree = tree + format!("{}\n", body).as_str();
                tree
            },
            Nodes(_, body, ref children) => {
                tree = tree + format!("{}\n", body).as_str();
                if children.len() > 0 {
                    let display_level = level + 1;
                    let indent_level = (0..display_level).map(|_| "+ ").collect::<String>();
                    for child_node in children {
                        tree = tree + indent_level.as_str() + child_node.display(display_level).as_str();
                    }
                }
                tree
            },
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::Point::{Cartesian};
    use super::BHTree::{Empty, Node, Nodes};

    #[test]
    fn bounds_new_default() {
        let b = Bounds::new(&Point::new());
        assert_eq!(b.lower, Cartesian(-1.0, -1.0, -1.0));
        assert_eq!(b.upper, Cartesian(1.0, 1.0, 1.0));
    }

    #[test]
    fn tree_new_default() {
        let t = BHTree::new();
        match t {
            Empty(bounds) => {
                assert_eq!(bounds.lower, Cartesian(-1.0, -1.0, -1.0));
                assert_eq!(bounds.upper, Cartesian(1.0, 1.0, 1.0));
            },
            _ => assert!(false),
        }
    }

    #[test]
    fn tree_insert_empty() {
        let mut t = BHTree::new();
        t.insert(Body { centre: Cartesian(0.0, 0.0, 0.0), mass: 100.0 });
        match t {
            Node(_, body) => assert_eq!(body.mass, 100f64),
            _ => assert!(false),
        }
    }

    #[test]
    fn tree_insert_node() {
        let mut t = BHTree::new();
        t.insert(Body { centre: Cartesian(0.8, 0.8, 0.8), mass: 100.0 });
        t.insert(Body { centre: Cartesian(0.4, 0.4, 0.4), mass: 100.0 });
        t.insert(Body { centre: Cartesian(-0.6, -0.6, -0.6), mass: 100.0 });
        match t {
            Nodes(_, body, children) => {
                assert_eq!(body.centre, Cartesian(0.2, 0.2, 0.2));
                assert_eq!(body.mass, 300f64);
                assert_eq!(children.len(), 8);
            },
            _ => assert!(false),
        }
    }
}
