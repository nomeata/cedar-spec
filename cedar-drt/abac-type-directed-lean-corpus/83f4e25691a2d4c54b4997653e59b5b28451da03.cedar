forbid(
  principal == a::"66",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")) == (ip("ecf2:36d1:d9c9:c9c9:ffcd:c932:c3c3:c3c3/65"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))) == (ip("0.0.0.0")))) && false) && false
};
