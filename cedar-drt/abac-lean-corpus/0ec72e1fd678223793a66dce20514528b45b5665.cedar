@A("")
permit(
  principal,
  action in [Action::"",Action::"ef"],
  resource == a::""
) when {
  true && (7668058319050768389.contains(principal))
};
