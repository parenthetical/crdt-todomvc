{}:
(import ./reflex-platform {}).project ({ pkgs, ... }: {
  packages = {
    crdt-todomvc = ./crdt-todomvc;
  };

  shells = {
    ghc = ["crdt-todomvc"];
    ghcjs = ["crdt-todomvc"];
  };
})
