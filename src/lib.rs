//! # Cons List
//!
//! Implementation of the immutable data structure the cons list in Rust, common
//! in Functional languages.
//!

use crate::List::{Cons, Nil};
use std::iter::FromIterator;

/// An immutable list.
#[derive(Debug, Default, PartialEq, PartialOrd)]
pub enum List<T> {
    #[default]
    Nil,
    Cons(T, Box<List<T>>),
}

/// Creates a `List` containing the arguments.
/// `cons!` allows `List`s to be defined with similar syntax to `Vec`s.
/// Create a `List` containing a given list of elements.
///
/// # Examples
///
#[macro_export]
macro_rules! cons {
    // Empty list
    [] => {
        Nil
    };

    // Singleton list
    [ $head:expr ] => {
        Cons($head, Box::new(Nil))
    };

    // Recursive case: more than one item
    [$head:expr, $($tail:expr),+] => {
        Cons($head, Box::new( cons!($($tail), +) ))
    };
 }

#[macro_export]
macro_rules! cons_rev {
[ $( $x:expr ), *] => {
        {
            let list = Nil;
            $(
                let list = Cons($x, Box::new(list));
            )*
            list
        }
    };
}

// Define the iterator struct for List
pub struct ListIntoIterator<T> {
    list: List<T>,
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = ListIntoIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        ListIntoIterator { list: self }
    }
}

impl<T> Iterator for ListIntoIterator<T> {
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
            .fold(Nil, |xs, x| Cons(x, Box::new(xs)))
            .into_iter() // Reverse the list again
            .fold(Nil, |xs, x| Cons(x, Box::new(xs)))
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
    Nil
}

/// Prepends `x` to the list `xs`.
///
/// Provides convenient alternative to defining a list e.g. `cons(1, nil())`
///
/// # Examples
/// ```
/// # use cons_list::cons;
/// # use cons_list::List::{Cons, Nil};
/// let list = cons![1, 2];
/// let list = cons(1, list);
/// assert_eq!(list, cons![1, 2]);
/// ```
pub fn cons<T>(x: T, xs: List<T>) -> List<T> {
    Cons(x, Box::new(xs))
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

    pub fn into_reverse(list: List<T>) -> List<T> {
        list.into_iter().fold(Nil, |xs, x| cons(x, xs))
    }

    pub fn reverse<'a>(list: &'a List<T>) -> List<&'a T> {
        list.fold(Nil, |xs, x| cons(x, xs))
    }

    /// Returns the length of the list
    ///
    /// # Examples
    /// ```
    /// # use cons_list::List::{Cons, Nil};
    /// # use cons_list::cons;
    /// let list = cons![1, 2, 3];
    /// assert_eq!(list.len(), 3);
    /// ```
    /// # Time complexity
    /// Takes O(n) time.
    pub fn len(&self) -> usize {
        self.count()
    }

    pub fn is_empty(&self) -> bool {
        match self {
            Nil => true,
            _ => false,
        }
    }

    /// Pushes the value x to the given list.
    ///
    /// # Examples
    /// ```
    /// # use cons_list::List::{Cons, Nil};
    /// # use cons_list::cons;
    /// let mut list = cons![2, 3];
    /// list.push(1);
    /// assert_eq!(cons![1, 2, 3], list);
    /// ```
    /// # Time complexity
    /// Takes O(1) time.
    pub fn push(&mut self, x: T) {
        // Take ownership of self and replace it with the default Nil
        // value. This allows us to work with the original list value without
        // violating borrowing rules.
        let xs = std::mem::take(self);
        *self = Cons(x, Box::new(xs));
    }

    /// Pops the head of the list and returns it, or `None` if the list is empty
    ///
    /// # Examples
    /// ```
    /// let mut list = cons![1, 2, 3];
    /// let head = list.pop();
    ///
    /// assert_eq!(Some(1), head);
    /// assert_eq!(cons![2, 3], list);
    /// ```
    /// # Time complexity
    /// Takes O(1) time.
    fn pop(&mut self) -> Option<T> {
        // Take ownership of self and replace it with the default Nil
        // value. This allows us to work with the original list value without
        // violating borrowing rules.
        let list = std::mem::take(self);
        match list {
            Nil => None,
            Cons(head, tail) => {
                *self = *tail;
                Some(head)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construction() {
        let list = Cons(2, Box::new(Nil));

        println!("{:?}", list);

        assert_eq!(Cons(2, Box::new(Nil)), list);

        let list = Cons(1, Box::new(list));
        assert_eq!(Cons(1, Box::new(Cons(2, Box::new(Nil)))), list);
    }

    #[test]
    fn macro_empty() {
        let empty: List<i32> = Nil;

        assert_eq!(empty, cons![]);
    }

    #[test]
    fn macro_singleton() {
        let singleton: List<i32> = Cons(1, Box::new(Nil));

        assert_eq!(singleton, cons![1]);
    }

    #[test]
    fn macro_test() {
        let xs = Cons(2, Box::new(Cons(3, Box::new(Nil))));
        assert_eq!(cons![2, 3], xs);

        let xs = Cons(1, Box::new(xs));
        assert_eq!(cons![1, 2, 3], xs);
    }

    #[test]
    fn iter_test() {
        let xs = cons![Some(1), Some(2), Some(3)];

        for x in xs.enumerate() {
            println!("{:?}", x);
        }

        for x in &xs {
            println!("{:?}", x);
        }

        assert_eq!(xs, cons![Some(1), Some(2), Some(3)])
    }

    #[test]
    fn into_iter_test() {
        let xs = cons![1, 2, 3];
        let vector: Vec<i32> = xs.into_iter().collect();

        assert_eq!(vec![1, 2, 3], vector);
    }

    #[test]
    fn from_iter() {
        let xs = cons![1, 2, 3];
        let ys: List<i32> = xs.map(|x| x * 2).collect();

        assert_eq!(cons![2, 4, 6], ys)
    }

    #[test]
    fn len_test() {
        let xs: List<i32> = cons![];
        assert_eq!(0, xs.len());

        let xs = cons![2];
        assert_eq!(1, xs.len());

        let xs = cons![1, 2, 3, 4];
        assert_eq!(4, xs.len());

        let xs = cons![Some(1), Some(2), Some(3)];
        assert_eq!(3, xs.len());
    }

    #[test]
    fn push_test() {
        let mut list = cons![2, 3, 4];
        list.push(1);
        assert_eq!(cons![1, 2, 3, 4], list);
    }

    #[test]
    fn pop_test() {
        let mut list = cons![1, 2, 3];
        let head = list.pop();

        assert_eq!(Some(1), head);
        assert_eq!(cons![2, 3], list);
    }

    #[test]
    fn reverse_test() {
        let list = cons![None, Some(1), Some(2), Some(3)];
        let list = List::into_reverse(list);

        assert_eq!(cons![Some(3), Some(2), Some(1), None], list);
    }
}
