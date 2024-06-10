//! # rust-cons-list
//!
//! Implementation of a singly linked, recursively defined list.
//!
//! This crate extends the implementation of the basic cons list found straight in
//! the Rust Book to offer some conveniences similar to those implemented for the
//! `Vec`. Specifically, a `list!` macro for easy instantiation manual implementations
//!
//! ## Usage
//!
//! ### Creating a new list
//!
//! A macro `list!` is defined to allow for easy instantiation. Otherwise the
//! `cons()` and `nil()` functions are provided as an alternative.
//!
//! ``` rust
//! use cons_list::{List, list, nil, cons};
//! use cons_list::List::{Cons, Nil};
//!
//! let mut xs = list![1, 2, 3];
//! let ys = cons(1, cons(2, cons(3, nil())));
//! assert_eq!(xs, ys);
//!
//! // Defined manually
//! assert_eq!(xs, Cons(1, Box::new(Cons(2, Box::new(Cons(3, Box::new(Nil)))))));
//!
//! xs.push(0);
//! assert_eq!(xs, list![0, 1, 2, 3]);
//! assert_eq!(xs.len(), 4);
//! assert_eq!(xs.is_empty(), false);
//!
//! xs.pop();
//! assert_eq!(xs, list![1, 2, 3]);
//! xs.append(list![4, 5, 6]);
//! assert_eq!(xs, list![1, 2, 3, 4, 5, 6]);
//! xs.reverse();
//! assert_eq!(xs, list![6, 5, 4, 3, 2, 1]);
//!
//! let ys: List<i32> = xs.map(|x| x * 2).collect();
//! assert_eq!(ys, list![12, 10, 8, 6, 4, 2]);
//!
//! let zs: List<i32> = xs.into_iter().filter(|x| *x < 4).collect();
//! assert_eq!(zs, list![3, 2, 1]);
//! assert_eq!(zs.fold(0, |acc, x| acc + x * 2), 12);
//! ```
use std::fmt::Display;

pub use crate::List::{Cons, Nil};

/// An immutable list.
#[derive(Debug, Default, PartialEq, PartialOrd)]
pub enum List<T> {
    #[default]
    Nil,
    Cons(T, Box<List<T>>),
}

/// Creates a [List] containing a given list of elements.
///
/// [list!] macro allows [List]s to be defined with similar syntax to the [vec!] macro.
///
/// # Examples
/// ```
/// # use cons_list::{List, list};
/// # use cons_list::List::{Cons, Nil};
/// let list = list![1, 2];
/// assert_eq!(list, Cons(1,Box::new(Cons(2, Box::new(Nil)))));
/// ```
#[macro_export]
macro_rules! list {
    // Empty list.
    [] => {
        List::Nil
    };

    // Singleton list.
    [ $head:expr ] => {
        List::Cons($head, Box::new(Nil))
    };

    // Recursive case: more than one item.
    [$head:expr, $($tail:expr),+] => {
        List::Cons($head, Box::new( list!($($tail), +) ))
    };
 }

/// Create a [List] containing a given list of elements in reverse.
///
/// # Examples
/// ```
/// # use cons_list::{list_rev, List};
/// # use cons_list::List::{Cons, Nil};
/// let list = list_rev![1, 2];
/// assert_eq!(list, Cons(2,Box::new(Cons(1, Box::new(Nil)))));
/// ```
#[macro_export]
macro_rules! list_rev {
[ $( $x:expr ), *] => {
        {
            let list = List::Nil;
            $(
                let list = List::Cons($x, Box::new(list));
            )*
            list
        }
    };
}

impl<T: Display> Display for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = self;

        fn is_empty<T>(list: &Box<List<T>>) -> bool {
            match **list {
                List::Nil => true,
                List::Cons(_, _) => false,
            }
        }

        write!(f, "list![").ok();
        while let Cons(head, tail) = list {
            // Peek to see if we're at the end of the list.
            // tail is a shared reference, is_empty borrows another reference.
            if is_empty(tail) {
                write!(f, "{}", head).ok();
            } else {
                write!(f, "{}, ", head).ok();
            }
            list = tail;
        }
        write!(f, "]")
    }
}

// IntoIterator implementation enables usage of Lists in loops.
impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = ListIntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        ListIntoIter { list: self }
    }
}

// Define the iterator struct for List.
pub struct ListIntoIter<T> {
    list: List<T>,
}

impl<T> Iterator for ListIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        // Take ownership of self.list and replace it with the default Nil
        // value. This allows us to work with the original list value without
        // violating borrowing rules.
        let list = std::mem::take(&mut self.list);
        match list {
            Cons(head, tail) => {
                self.list = *tail; // Move ownership of the tail back to self.list
                Some(head)
            }
            Nil => None,
        }
    }
}

// Enables direct usage of many built-in iterator functions directly on Lists.
impl<'a, T> Iterator for &'a List<T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Nil => None,
            Cons(head, tail) => {
                // replaces the contents of the reference self (which initially
                // points to the whole list) with xs (the rest of the list).
                // This "moves" the reference down the list.
                let _ = std::mem::replace(self, tail);
                Some(head)
            }
        }
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<U: IntoIterator<Item = T>>(iter: U) -> Self {
        iter.into_iter() // Results in a reversed list
            .fold(Nil, |xs, x| cons(x, xs))
            .into_iter() // Reverse the list again
            .fold(Nil, |xs, x| cons(x, xs))
    }
}

/// Returns the empty list, synonymous with [List::new]
///
/// Provides convenient alternative to defining a list e.g. `cons(1, nil())`
///
/// # Examples
/// ```
/// # use cons_list::{nil, List};
/// # use cons_list::List::{Cons, Nil};
/// let list: List<i32> = nil();
/// assert_eq!(list, Nil);
/// ```
pub fn nil<T>() -> List<T> {
    List::Nil
}

/// Prepends `x` to the list `xs`.
///
/// Provides convenient alternative to defining a list e.g. `cons(1, nil())`
///
/// # Examples
/// ```
/// # use cons_list::{list, cons, List};
/// # use cons_list::List::{Cons, Nil};
/// let list = list![2, 3];
/// let list = cons(1, list);
/// assert_eq!(list, list![1, 2, 3]);
/// ```
pub fn cons<T>(x: T, xs: List<T>) -> List<T> {
    List::Cons(x, Box::new(xs))
}

impl<T> List<T> {
    /// Creates a new empty list, synonymous with [nil]
    ///
    /// # Examples
    /// ```
    /// # use cons_list::List::{Cons, Nil};
    /// # use cons_list::{cons, List};
    /// let list: List<i32> = List::new();
    /// assert_eq!(list, Nil);
    /// ```
    pub fn new() -> List<T> {
        Nil
    }

    /// Takes ownership of the input and returns a reverse of its elements
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{List, list};
    /// # use cons_list::List::{Cons, Nil};
    /// let list = list![None, Some(1), Some(2), Some(3)];
    /// let list = List::into_rev(list);
    /// assert_eq!(list![Some(3), Some(2), Some(1), None], list);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn into_rev(list: List<T>) -> List<T> {
        list.into_iter().fold(Nil, |xs, x| cons(x, xs))
    }

    /// Returns a reversed list of references to the input list
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{List, list};
    /// # use cons_list::List::{Cons, Nil};
    /// let list = list![None, Some(1), Some(2), Some(3)];
    /// let list = List::borrow_rev(&list);
    /// assert_eq!(list![&Some(3), &Some(2), &Some(1), &None], list);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn borrow_rev<'a>(list: &'a List<T>) -> List<&'a T> {
        list.fold(Nil, |xs, x| cons(x, xs))
    }

    /// Returns `true` if the list contains no elements.
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{list, List};
    /// let list: List<i32> = list![];
    /// assert!(list.is_empty());
    /// ```
    /// # Time complexity
    /// Takes O(1) time.
    pub fn is_empty(&self) -> bool {
        match self {
            Nil => true,
            _ => false,
        }
    }

    /// Returns the length of the list
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{list, List};
    /// # use cons_list::List::{Cons, Nil};
    /// let list = list![1, 2, 3];
    /// assert_eq!(list.len(), 3);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn len(&self) -> usize {
        self.count()
    }

    /// Returns the last element of the list, or `None` if it's empty.
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{list, List};
    /// # use cons_list::List::{Cons, Nil};
    /// let list = list![1, 2, 3];
    /// let last = list.last();
    ///
    /// assert_eq!(Some(&3), last);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn last(&self) -> Option<&T> {
        // Take ownership of self and replace it with the default Nil value.
        let mut last = None;
        let mut next = self;
        while let Cons(x, xs) = next {
            last = Some(x);
            next = xs;
        }

        last
    }

    /// Pushes the value x to the given list.
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{list, List};
    /// # use cons_list::List::{Cons, Nil};
    /// let mut list = list![2, 3];
    /// list.push(1);
    /// assert_eq!(list![1, 2, 3], list);
    /// ```
    /// # Time complexity
    /// Takes O(1) time.
    pub fn push(&mut self, x: T) {
        // Take ownership of self and replace it with the default Nil value.
        // This allows us to work with the original list value without violating
        // borrowing rules.
        let xs = std::mem::take(self);
        *self = Cons(x, Box::new(xs));
    }

    /// Pops the head of the list and returns it, or `None` if the list is empty
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{list, List};
    /// # use cons_list::List::{Cons, Nil};
    /// let mut list = list![1, 2, 3];
    /// let head = list.pop();
    ///
    /// assert_eq!(Some(1), head);
    /// assert_eq!(list![2, 3], list);
    /// ```
    /// # Time complexity
    /// Takes O(1) time.
    pub fn pop(&mut self) -> Option<T> {
        // Take ownership of self and replace it with the default Nil value.
        let list = std::mem::take(self);
        match list {
            Nil => None,
            Cons(head, tail) => {
                *self = *tail;
                Some(head)
            }
        }
    }

    /// Appends `list` to self;
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{List, list};
    /// # use cons_list::List::{Cons, Nil};
    /// let mut xs = list![1, 2, 3];
    /// let ys = list![4, 5, 6];
    ///
    /// xs.append(ys);
    /// assert_eq!(list![1, 2, 3, 4, 5, 6], xs);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn append(&mut self, list: List<T>) {
        let mut curr = self;

        while let Cons(_, next) = curr {
            curr = next;
        }

        let _ = std::mem::replace(curr, list);
    }

    /// Reverses the order of elements in the list
    ///
    /// # Examples
    /// ```
    /// # use cons_list::{List, list};
    /// # use cons_list::List::{Cons, Nil};
    /// let mut list = list![None, Some(1), Some(2), Some(3)];
    /// list.reverse();
    /// assert_eq!(list![Some(3), Some(2), Some(1), None], list);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn reverse(&mut self) {
        let list = std::mem::take(self);
        *self = list.into_iter().fold(Nil, |xs, x| cons(x, xs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construction() {
        let list = Cons(2, Box::new(Nil));
        assert_eq!(list, Cons(2, Box::new(Nil)));

        let list = Cons(1, Box::new(list));
        assert_eq!(list, Cons(1, Box::new(Cons(2, Box::new(Nil)))));
    }

    #[test]
    fn macro_empty() {
        let empty: List<i32> = Nil;
        assert_eq!(empty, list![]);
    }

    #[test]
    fn macro_singleton() {
        let singleton: List<i32> = Cons(1, Box::new(Nil));

        assert_eq!(singleton, list![1]);
    }

    #[test]
    fn macro_multiple() {
        let xs = Cons(2, Box::new(Cons(3, Box::new(Nil))));
        assert_eq!(xs, list![2, 3]);

        let xs = Cons(1, Box::new(xs));
        assert_eq!(xs, list![1, 2, 3]);
    }

    #[test]
    fn display() {
        let xs = list![1, 2, 3, 4, 5];
        assert_eq!("list![1, 2, 3, 4, 5]", xs.to_string());
    }

    #[test]
    fn iter() {
        let xs = list![Some(1), Some(2), Some(3)];

        for x in xs.enumerate() {
            println!("{:?}", x);
        }

        for x in &xs {
            println!("{:?}", x);
        }

        assert_eq!(xs, list![Some(1), Some(2), Some(3)])
    }

    #[test]
    fn for_loop() {
        let xs = list![1, 2, 3, 4, 5];
        let mut ys: List<i32> = nil();
        for x in xs {
            ys.push(x * 2);
        }

        assert_eq!(ys, list![10, 8, 6, 4, 2])
    }

    #[test]
    fn into_iter() {
        let xs = list![1, 2, 3];
        let v: Vec<i32> = xs.into_iter().collect();

        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn from_iter() {
        let xs = list![1, 2, 3];
        let ys: List<i32> = xs.map(|x| x * 2).collect();

        assert_eq!(ys, list![2, 4, 6])
    }

    #[test]
    fn len() {
        let xs: List<i32> = list![];
        assert_eq!(0, xs.len());

        let xs = list![2];
        assert_eq!(1, xs.len());

        let xs = list![1, 2, 3, 4];
        assert_eq!(4, xs.len());

        let xs = list![Some(1), Some(2), Some(3)];
        assert_eq!(3, xs.len());
    }

    #[test]
    fn push() {
        let mut list = list![2, 3, 4];
        list.push(1);
        assert_eq!(list, list![1, 2, 3, 4]);
    }

    #[test]
    fn pop() {
        let mut list = list![1, 2, 3];
        let head = list.pop();

        assert_eq!(head, Some(1));
        assert_eq!(list, list![2, 3]);
    }

    #[test]
    fn into_rev() {
        let list = list![None, Some(1), Some(2), Some(3)];
        let list = List::into_rev(list);

        assert_eq!(list![Some(3), Some(2), Some(1), None], list);
    }

    #[test]
    fn borrow_rev() {
        let list = list![None, Some(1), Some(2), Some(3)];
        let list = List::borrow_rev(&list);

        println!("{:?}", list);

        assert_eq!(list![&Some(3), &Some(2), &Some(1), &None], list);
    }

    #[test]
    fn append() {
        let mut xs = list![Some(1), Some(2)];
        let ys = list![Some(3), Some(4), Some(5)];
        xs.append(ys);

        assert_eq!(xs, list![Some(1), Some(2), Some(3), Some(4), Some(5)]);
    }

    #[test]
    fn filter() {
        let xs = list![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let ys: List<i32> = xs.into_iter().filter(|x| *x <= 5).collect();
        let zs: List<&i32> = ys.filter(|y| **y >= 3).collect();

        assert_eq!(ys, list![1, 2, 3, 4, 5]);
        assert_eq!(zs, list![&3, &4, &5]);
    }

    #[test]
    fn map() {
        let xs = list![1, 2, 3, 4, 5];
        let ys: List<i32> = xs.map(|x| x * 2).collect();

        assert_eq!(ys, list![2, 4, 6, 8, 10]);
    }

    #[test]
    fn fold() {
        let xs = list![Some(1), None, Some(3), None, Some(5)];
        let sum = xs.fold(0, |sum, x| match x {
            Some(y) => y + sum,
            None => sum,
        });
        assert_eq!(sum, 9);
    }
}
