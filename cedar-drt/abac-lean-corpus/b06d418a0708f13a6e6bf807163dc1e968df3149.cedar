forbid(
  principal in a::"",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && ("" in "")) && "j"
};
