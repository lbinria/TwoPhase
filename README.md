# Two Phase

An implementation of Two phase protocol (simplified) specification.

## Prerequisite

- Java >= 17.0.0
- Apache maven >= 3.6.3
- Python >= 3.9.12

Install trace_validation_tools scripts.

## Run

Run implementation alone:

`python run_impl.py`

Run implementation following by trace validation:

`python trace_validation_pipeline.py`

## Project structure

spec/ directory contains Two phase TLA+ specification and Two phase specification for trace validation.

src/ directory contains a java implementation of Two phase spec.