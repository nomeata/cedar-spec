forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::"\u{17}\0"
) when {
  (true && (((a::"\u{17}\0" in (-9187201950435737472)) in (!context)) in action)) && ("".containsAll(false))
};
