forbid(
  principal is Ahgnj in Ahgnj::"",
  action in [Action::"action"],
  resource is Ahgnj in Ahgnj::""
) when {
  (true && ((if (principal["p"]) then principal else principal)["p"])) && principal
};
