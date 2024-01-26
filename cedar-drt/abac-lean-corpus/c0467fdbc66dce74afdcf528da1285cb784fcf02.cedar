@V1111U300("\0\0\0")
forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (false && ((a::"".contains(context)) == A::Ah100::"")) && action
};
