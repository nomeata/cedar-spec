permit(
  principal == a::"jj",
  action in [Action::"nks-`"],
  resource is a in a::"jj"
) when {
  (true && [Action::"nks-`".isMulticast(), Aq100::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0", principal == principal, principal, principal, principal]) && a::""
};
