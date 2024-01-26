@B("!\0\0\0\0\0")
@r("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((true || (principal in resource)) || ((resource in resource) || true))) && true) && ((true || (!((-7032538600120082786) < 26214))) || false)
};
