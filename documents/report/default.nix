{
  self,
  system,
  pkgs,
}:
  let report = pkgs.buildTypstDocument {
    name = "report";
    src = ./.;
    typstEnv = p: with p; [
      gruvy_2_1_0
      zebraw_0_5_5
      fletcher_0_5_8
      xarrow_0_3_1
      theorion_0_4_0
      oxifmt_0_2_1 # Nixpkgs support for typst is sort of janky
    ];
    creationTimestamp = self.lastModified;
    fonts = [
      pkgs.roboto
    ];
  };
in {
  packages.default = report; 

  devShells.default = pkgs.mkShellNoCC {
    inputsFrom = [ report ];
    packages = [
      pkgs.tinymist
      pkgs.typstyle
      pkgs.harper
    ];
  };
}
