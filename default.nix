let
  pkgs = import <nixpkgs> {};
  src = pkgs.fetchFromGitHub {
    owner = "SSProve";
    repo = "ssprove";
    rev = "4e851b76fc6dd3ff50616e8dace4cd832a480e80"; # 05-12-2025
    sha256 = "6l1KeE5I5cqWHaXVZW3Is2aMbPJnVhOEad+3SuBX9xs=";
  };
in import "${src}/default.nix"
