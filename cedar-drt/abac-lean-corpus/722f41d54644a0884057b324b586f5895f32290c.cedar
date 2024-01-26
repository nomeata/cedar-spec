forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (false && (a::"" in a::"")) && a::""
};
