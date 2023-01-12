# stable_matching

Implementation of the Gale-Shapley algorithm, as described on page 6 of _Algorithm Design_ by Kleinberg and Tardos.

Client supplies two slices representing each of the two groups seeking a match, and distance functions indicating preferences. 
A `Vec` of pairs of slice indices is returned to indicate the stable matches.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contributions

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
