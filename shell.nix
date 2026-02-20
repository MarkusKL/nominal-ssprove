let
  args = { bundle = "9.1"; inNixShell = true; };
  nixpkgs = import ./default.nix args;
  pkgs = nixpkgs.pkgs;
  vimCustom = pkgs.callPackage ({ vim-full, vimPlugins }:
    (vim-full.customize {
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
            set number
            " set relativenumber
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
    })) {};
in pkgs.mkShell {
  packages = with pkgs; [
    coqPackages.coq
    # coqPackages.coqide
    # coqPackages.coq-lsp
    coqPackages.ssprove
    vimCustom
  ];
}
