forbid(
  principal is a in a::"cont",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("0.0.0.0")).isMulticast()) then [] else []) == [])) && false) && true
};
