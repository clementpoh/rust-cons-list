# rust-cons-list

Implementation of the data structure the cons list in Rust. It is essentially a
linked list defined recursively and popular in functional programming languages
like Lisp and Haskell. Chapter 15 of the [Rust
Book](https://doc.rust-lang.org/book/ch15-01-box.html) introduces the concept
and the basic implementation of the list in Rust.

While the linked list is disfavored in Rust, it's a familiar structure to many
functional programmers.

This library extends the implementation of the basic cons list found in the Rust
Book to offer conveniences similar to those implemented for the vector.

## Usage

### Definition

The type definition is lifted straight out of the Book

``` rust
#[derive(Debug, Default, PartialEq, PartialOrd)]
enum List<T> {
    #[default]
    Nil,
    Cons(T, Box<List<T>>),
}
```

### Creating a new list

A macro is defined to allow for easy instantiation.

``` rust
  let list = cons![1, 2, 3]
  assert_eq!(list, Cons(1, Cons(2, Box::new(Cons(3, Box::new(Nil))))));
```
