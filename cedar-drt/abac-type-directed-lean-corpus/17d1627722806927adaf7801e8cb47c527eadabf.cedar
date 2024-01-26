forbid(
  principal == a::"f\066\0\0",
  action in [Action::"action"],
  resource is a in a::"f\066\0\0"
) when {
  false
};
