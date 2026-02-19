let
  pkgs = import <nixpkgs> {};
  src = pkgs.fetchFromGitHub {
    owner = "SSProve";
    repo = "ssprove";
    rev = "58909a89e4542acc96c7e48396ee14dddcbc6177"; # 04-02-2026
    sha256 = "otYCpwCdBn4LF7FSjEGx3oVvFC/okgDkNayoGkRoXeI=";
  };
in import "${src}/default.nix"
