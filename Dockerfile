FROM nixos/nix
RUN mkdir -p ~/.config/nix
COPY .devcontainer/nix.conf shell.nix default.nix /mnt/
RUN mv /mnt/nix.conf ~/.config/nix/
WORKDIR /mnt
RUN nix-shell
COPY . /mnt/
ENTRYPOINT ["nix-shell"]
