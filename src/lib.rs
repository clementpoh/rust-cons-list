//! # Cons List
//!
//! Implementation of the immutable data structure the cons list in Rust, common
//! in Functional languages.
//!
use crate::List::{Cons, Nil};

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
/// # use cons_list::list;
/// # use cons_list::List::{Cons, Nil};
/// let list = list![1, 2];
/// assert_eq!(list, Cons(1,Box::new(Cons(2, Box::new(Nil)))));
/// ```
#[macro_export]
macro_rules! list {
    // Empty list.
    [] => {
        Nil
    };

    // Singleton list.
    [ $head:expr ] => {
        Cons($head, Box::new(Nil))
    };

    // Recursive case: more than one item.
    [$head:expr, $($tail:expr),+] => {
        Cons($head, Box::new( list!($($tail), +) ))
    };
 }

/// Create a [List] containing a given list of elements in reverse.
///
/// # Examples
/// ```
/// # use cons_list::list_rev;
/// # use cons_list::List::{Cons, Nil};
/// let list = list_rev![1, 2];
/// assert_eq!(list, Cons(2,Box::new(Cons(1, Box::new(Nil)))));
/// ```
#[macro_export]
macro_rules! list_rev {
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

// IntoIterator implementation enables usage of Lists in loops.
impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = ListIntoIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        ListIntoIterator { list: self }
    }
}

// Define the iterator struct for List.
pub struct ListIntoIterator<T> {
    list: List<T>,
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
    Nil
}

/// Prepends `x` to the list `xs`.
///
/// Provides convenient alternative to defining a list e.g. `cons(1, nil())`
///
/// # Examples
/// ```
/// # use cons_list::{list, cons};
/// # use cons_list::List::{Cons, Nil};
/// let list = list![2, 3];
/// let list = cons(1, list);
/// assert_eq!(list, list![1, 2, 3]);
/// ```
pub fn cons<T>(x: T, xs: List<T>) -> List<T> {
    Cons(x, Box::new(xs))
}

impl<T: core::fmt::Debug> List<T> {
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
    /// # use cons_list::List::{Cons, Nil};
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
    /// # use cons_list::list;
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
    /// # use cons_list::list;
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
    /// # use cons_list::list;
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
    /// # use cons_list::list;
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

        println!("{:?}", list);

        assert_eq!(Cons(2, Box::new(Nil)), list);

        let list = Cons(1, Box::new(list));
        assert_eq!(Cons(1, Box::new(Cons(2, Box::new(Nil)))), list);
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
    fn macro_test() {
        let xs = Cons(2, Box::new(Cons(3, Box::new(Nil))));
        assert_eq!(list![2, 3], xs);

        let xs = Cons(1, Box::new(xs));
        assert_eq!(list![1, 2, 3], xs);
    }

    #[test]
    fn iter_test() {
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
    fn into_iter_test() {
        let xs = list![1, 2, 3];
        let vector: Vec<i32> = xs.into_iter().collect();

        assert_eq!(vec![1, 2, 3], vector);
    }

    #[test]
    fn from_iter() {
        let xs = list![1, 2, 3];
        let ys: List<i32> = xs.map(|x| x * 2).collect();

        assert_eq!(list![2, 4, 6], ys)
    }

    #[test]
    fn len_test() {
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
    fn push_test() {
        let mut list = list![2, 3, 4];
        list.push(1);
        assert_eq!(list![1, 2, 3, 4], list);
    }

    #[test]
    fn pop_test() {
        let mut list = list![1, 2, 3];
        let head = list.pop();

        assert_eq!(Some(1), head);
        assert_eq!(list![2, 3], list);
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
}
