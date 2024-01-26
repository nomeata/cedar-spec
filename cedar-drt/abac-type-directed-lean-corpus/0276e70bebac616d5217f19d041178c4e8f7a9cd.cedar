permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (!({"\0\0\0\u{1}": false, "61&3": false, "": decimal("0.255")} has ""))
};
