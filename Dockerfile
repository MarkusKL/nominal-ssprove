FROM nixos/nix
RUN mkdir -p ~/.config/nix
RUN echo 'experimental-features = nix-command flakes' >> ~/.config/nix/nix.conf
RUN echo 'substituters = https://cache.nixos.org https://coq.cachix.org https://coq-community.cachix.org https://math-comp.cachix.org' >> ~/.config/nix/nix.conf
RUN echo 'trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= coq.cachix.org-1:5QW/wwEnD+l2jvN6QRbRRsa4hBHG3QiQQ26cxu1F5tI= coq-community.cachix.org-1:WBDHojv8FM6nI4ZMh43X+2g6j4WpAn+dFhjhWmLCgnA= math-comp.cachix.org-1:ZoAy3dSWncrBPpEsNHa1Rbio0Oly3TFrZXlVTdofbQU=' >> ~/.config/nix/nix.conf

COPY shell.nix default.nix /mnt/
COPY .nix/ /mnt/.nix/
WORKDIR /mnt
RUN nix-shell
COPY . /mnt/
ENTRYPOINT ["nix-shell"]
