permit(
  principal is a in a::"7",
  action in [Action::"action"],
  resource == a::"7"
) when {
  (true && ((if ((ip("239.255.255.54/24")).isMulticast()) then 0 else 0) == 0)) && false
};
