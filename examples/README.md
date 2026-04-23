# Vera Examples

32 example programs demonstrating Vera's features. All examples pass `vera check` and `vera verify`.

## Running Examples

Examples with a `main` function run directly:

```bash
vera run examples/hello_world.vera
```

Examples without `main` export named functions — use `--fn` to call them:

```bash
vera run examples/factorial.vera --fn factorial -- 10
```

## Example Index

### Getting Started

| Example | Run | Demonstrates |
|---------|-----|-------------|
| `hello_world.vera` | `vera run examples/hello_world.vera` | IO.print, basic program structure |
| `safe_divide.vera` | `vera run examples/safe_divide.vera --fn safe_divide -- 3 10` | Preconditions, postconditions, division by zero prevention |
| `absolute_value.vera` | `vera run examples/absolute_value.vera --fn absolute_value -- -5` | If/else, contracts, simple function |
| `factorial.vera` | `vera run examples/factorial.vera --fn factorial -- 10` | Recursion, `decreases` termination measure |
| `fizzbuzz.vera` | `vera run examples/fizzbuzz.vera` | String interpolation, IO effect, loops via recursion |
| `increment.vera` | `vera run examples/increment.vera --fn increment` | State effect, get/put operations |

### Type System

| Example | Run | Demonstrates |
|---------|-----|-------------|
| `refinement_types.vera` | `vera run examples/refinement_types.vera --fn test_refine` | Refinement types (`PosInt`, `Percentage`, `NonEmptyArray`) |
| `pattern_matching.vera` | `vera run examples/pattern_matching.vera --fn test_match` | Match expressions, ADT destructuring |
| `generics.vera` | `vera run examples/generics.vera --fn test_generics` | Parametric polymorphism, generic ADTs |
| `quantifiers.vera` | `vera run examples/quantifiers.vera --fn test_process` | Universal/existential quantifiers in contracts |
| `closures.vera` | `vera run examples/closures.vera --fn test_closure` | First-class functions, anonymous functions |

### Effects

| Example | Run | Demonstrates |
|---------|-----|-------------|
| `effect_handler.vera` | `vera run examples/effect_handler.vera` | State, Exn effects, handler blocks, resume |
| `io_operations.vera` | `vera run examples/io_operations.vera` | IO.print, IO.read_file, IO.write_file, IO.exit |
| `file_io.vera` | `vera run examples/file_io.vera` | File read/write with error handling |
| `async_futures.vera` | `vera run examples/async_futures.vera` | Async effect, Future type, concurrent composition |
| `http.vera` | `vera run examples/http.vera` | Http.get, JSON parsing, network I/O (requires network) |

### Data Structures

| Example | Run | Demonstrates |
|---------|-----|-------------|
| `list_ops.vera` | `vera run examples/list_ops.vera --fn test_list` | Recursive ADTs (linked list), sum, length |
| `mutual_recursion.vera` | `vera run examples/mutual_recursion.vera --fn is_even -- 4` | Mutually recursive functions (is_even/is_odd) |
| `collections.vera` | `vera run examples/collections.vera` | Map and Set operations, word frequency analysis |

### Standard Library

| Example | Run | Demonstrates |
|---------|-----|-------------|
| `string_ops.vera` | `vera run examples/string_ops.vera` | String search, transform, split, join |
| `string_utilities.vera` | `vera run examples/string_utilities.vera --fn padded_id` | string_chars, string_lines, string_words, string_pad_*, string_trim_*, string_reverse, char_to_*, is_digit/alpha/alphanumeric/whitespace/upper/lower |
| `regex.vera` | `vera run examples/regex.vera` | regex_match, regex_find, regex_find_all, regex_replace |
| `markdown.vera` | `vera run examples/markdown.vera` | md_parse, pattern matching on MdBlock ADT |
| `json.vera` | `vera run examples/json.vera` | json_parse, json_get, Json ADT, API response handling |
| `base64.vera` | `vera run examples/base64.vera` | base64_encode, base64_decode |
| `url_encoding.vera` | `vera run examples/url_encoding.vera` | url_encode, url_decode |
| `url_parsing.vera` | `vera run examples/url_parsing.vera` | url_parse, UrlParts ADT |

### Advanced

| Example | Run | Demonstrates |
|---------|-----|-------------|
| `modules.vera` | `vera run examples/modules.vera --fn clamp -- 100 0 42` | Module imports, qualified calls, cross-file composition |
| `gc_pressure.vera` | `vera run examples/gc_pressure.vera` | GC behaviour under allocation pressure |
