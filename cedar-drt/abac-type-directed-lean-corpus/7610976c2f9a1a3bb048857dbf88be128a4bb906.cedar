forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((ip(if false then "6666" else "")) == (ip(if true then "" else "")))) && ((ip(if true then "" else "")) == (ip(if false then "" else "")))) && false
};
