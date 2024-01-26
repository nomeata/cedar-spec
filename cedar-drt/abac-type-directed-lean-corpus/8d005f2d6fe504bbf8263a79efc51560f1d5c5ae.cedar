forbid(
  principal is a in a::"\'6\0\0666",
  action in [Action::""],
  resource is a in a::"\'6\0\0666"
) when {
  true && (action has "")
};
