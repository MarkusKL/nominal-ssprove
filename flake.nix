# derived from ssprove/flake.nix
{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    let
      nominalsspPkg = { lib, mkCoqDerivation, coq
                  , equations, extructures, deriving
                  , mathcomp-analysis, mathcomp-ssreflect
                  , ssprove }:
        mkCoqDerivation {
          pname = "nominal-ssprove";
          owner = "MarkusKL";
          version = "1.1.1";
          src = ./.;
          propagatedBuildInputs = [ ssprove ];
          meta = {
            description = "Extending SSProve with nominals";
            license = lib.licenses.mit;
          };
        };
      vimPkg = { vim_configurable, vimPlugins }:
        (vim_configurable.customize {
            name = "vim";
            vimrcConfig = {
              packages.myVimPackage.start = with vimPlugins; [
                Coqtail
                vim-unicoder
              ];
              customRC = ''
                syntax on
                colorscheme default
                let &t_ut='''
                set relativenumber
                set tabstop=2
                set shiftwidth=2
                set softtabstop=2
                set expandtab
                set backspace=indent,eol,start
                filetype plugin on
                filetype indent on
                hi def CoqtailChecked      ctermbg=7
                hi def CoqtailSent         ctermbg=3
                hi def link CoqtailError   Error
                hi def link CoqtailOmitted coqProofAdmit
              '';
            };
        });
    in {
      overlays.default = final: prev: {
        coqPackages_8_19 = prev.coqPackages_8_19.overrideScope (self: super: {
          # mathcomp-ssreflect inherits this version
          # setting it to mathcomp-ssreflect does not work.
          # see my question on Zulip:
          # https://coq.zulipchat.com/#narrow/stream/290990-Nix-toolbox-devs-.26-users/topic/Loading.20inconsistency.20in.20mathcomp.20dependencies
          mathcomp = super.mathcomp.override { version = "2.2.0"; };
          nominal-ssprove = self.callPackage nominalsspPkg {};
        });
      };
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };
      in {
        packages.default = pkgs.coqPackages_8_19.nominal-ssprove;
        devShells.default = pkgs.stdenv.mkDerivation {
          name = "nominal-ssprove-shell";
          buildInputs = [
            pkgs.glibcLocales
            pkgs.coqPackages_8_19.coq
            pkgs.coqPackages_8_19.ssprove
            pkgs.coqPackages_8_19.coqide
            (pkgs.callPackage vimPkg {})
          ];
        };
      });
}
