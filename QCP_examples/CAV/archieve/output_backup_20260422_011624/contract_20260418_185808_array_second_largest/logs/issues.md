## Issues

- None at contract stage.

## Assumptions carried into the contract

- The raw statement’s “all elements are distinct” assumption is required for the intended mathematical meaning of “second largest”.
- The function is specified only over inputs with `n >= 2`.
- No separate overflow side-condition was added because the implementation only compares and returns existing array elements.
