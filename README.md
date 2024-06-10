# rust-cons-list

Implementation of a singly linked list in Rust. It is the recursively defined
list that is introduced in [Chapter 15 of the Rust Book][book]. While the linked
list is disfavored in Rust, it's a familiar structure to many functional
programmers.

This crate extends the implementation of the basic cons list found straight in
the Rust Book to offer some conveniences similar to those implemented for the
`Vec`. Specifically, a `list!` macro for easy instantiation manual implementations
of the following traits:

* `Display`
* `Iterator`
* `IntoIterator`
* `FromIterator`

Derived traits:

* `Debug`
* `Default`
* `PartialEq`
* `PartialOrd`

## Definition

The type definition is lifted straight out of the Book.

``` rust
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}
```

## Usage

### Creating a new list

A macro `list!` is defined to allow for easy instantiation. Otherwise the
`cons()` and `nil()` functions are provided as an alternative.

``` rust
  use cons_list::{List, list, nil, cons};
  use cons_list::List::{Cons, Nil};

  let xs = list![1, 2, 3];
  let ys = cons(1, cons(2, cons(3, nil())));

  assert_eq!(xs, ys);
  // Defined manually
  assert_eq!(xs, Cons(1, Box::new(Cons(2, Box::new(Cons(3, Box::new(Nil)))))));
```

### Manipulation

``` rust
  let mut xs = list![1, 2, 3];
  xs.push(0);
  assert_eq!(xs, list![0, 1, 2, 3]);

  assert_eq!(xs.len(), 4);
  assert_eq!(xs.is_empty(), false);

  xs.pop();
  assert_eq!(xs, list![1, 2, 3]);

  xs.append(list![4, 5, 6]);
  assert_eq!(xs, list![1, 2, 3, 4, 5, 6]);

  xs.reverse();
  assert_eq!(xs, list![6, 5, 4, 3, 2, 1]);

  let ys: List<i32> = xs.map(|x| x * 2).collect();
  assert_eq!(ys, list![12, 10, 8, 6, 4, 2]);

  let zs: List<i32> = xs.into_iter().filter(|x| *x < 4).collect();
  assert_eq!(zs, list![3, 2, 1]);

  assert_eq!(zs.fold(0, |acc, x| acc + x * 2), 12);
```

[book]: https://doc.rust-lang.org/book/ch15-01-box.html#more-information-about-the-cons-list
