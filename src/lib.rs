//! # Cons List
//!
//! Implementation of the functional structure the cons list in Rust.
use crate::List::{Cons, Nil};

#[derive(Debug, Default, PartialEq, PartialOrd)]
enum List<T> {
    #[default]
    Nil,
    Cons(T, Box<List<T>>),
}

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
struct ListIntoIterator<T> {
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
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter()
            .fold(Nil, |xs, x| List::push(x, xs))
            .into_iter()
            .fold(Nil, |xs, x| List::push(x, xs))
    }
}

impl<T> List<T> {
    fn new() -> List<T> {
        Nil
    }

    fn push(x: T, xs: List<T>) -> List<T> {
        Cons(x, Box::new(xs))
    }

    fn len(&self) -> usize {
        self.count()
    }
}

#[cfg(test)]
mod tests {
    use crate::List;
    use crate::List::Cons;
    use crate::List::Nil;

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
}
