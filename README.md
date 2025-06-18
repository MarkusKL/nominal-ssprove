# Nominal-SSProve

NEW: Begin [here](https://github.com/MarkusKL/nominal-ssprove-template) with the template and guide for using Nominal-SSProve.

Install dependencies by entering the nix development environment with command `nix develop` or using the docker environment as described below.
It is recommended to use the `coq`, `coq-community` and `math-comp` nix caches to significantly initial build time.

Check all project files using `make` and inspect files using vim (with Coqtail) or CoqIDE.

## Docker environment

Build image with Coq dependencies and enter shell with commands:

```
docker build -t nominal-ssprove .
docker run --rm -it nominal-ssprove
```

The project files are copied into the image, so changes made will not propagate to the host filesystem.
The final image is around 4GB in size and can be deleted with the command `docker rmi nominal-ssprove`.
