# Nominal-SSProve

As of [SSProve](https://github.com/ssprove/ssprove) v0.3.0, the features of
Nominal-SSProve have been completely integrated into SSProve. Therefore,
this repository has a new purpose: To showcase developments that use Nominal-SSProve.

[Nominal-SSProve v1.1.7](https://github.com/MarkusKL/nominal-ssprove/tree/v1.1.7) is the
last version of this repository with an independent development of nominal properties.
The properties as integrated into SSProve are found [here](https://github.com/SSProve/ssprove/tree/v0.3.0/theories/Crypt/nominal).

## Installation

Install dependencies by entering the nix development environment with command `nix-shell` or using the docker environment as described below.
It is recommended to use the `coq`, `coq-community` and `math-comp` nix caches to significantly reduce initial build time.

Check all project files using `make` and inspect files using vim (with Coqtail) or CoqIDE.

### Docker Environment

Build image with Coq dependencies and enter shell with commands:

```
docker build -t nominal-ssprove .
docker run --rm -it nominal-ssprove
```

The project files are copied into the image, so changes made will not propagate to the host filesystem.
The final image is around 4GB in size and can be deleted with the command `docker rmi nominal-ssprove`.

## Additional Examples

* Sigma-protocols in Nominal-SSProve:
    [MarkusKL/ssprove-sigma](https://github.com/MarkusKL/ssprove-sigma/tree/master)
* PKE-example in SSProve:
    [SSProve/ssprove](https://github.com/SSProve/ssprove/tree/v0.3.0/theories/Crypt/examples/PKE)

Student projects using Nominal-SSProve:

* Development of DDH and KEM based CKA:
    [hrallil/nominal-ssprove](https://github.com/hrallil/nominal-ssprove/tree/master/theories/Example/CKA)
* Cryptobox in SSProve based on [Bringing SSPs to EC](https://eprint.iacr.org/2021/326.pdf):
    [Myssenberg/nominal-ssprove](https://github.com/Myssenberg/nominal-ssprove/tree/master/theories/Cryptobox)
* Building Commitment Schemes from Sigma-protocols:
    [petersabroe/thesis](https://github.com/petersabroe/thesis/tree/main/project/theories)

