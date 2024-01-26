permit(
  principal,
  action in [Action::"action"],
  resource == a::"vz6.6"
) when {
  ((true && ((ip(action["z"])).isIpv4())) && ((if false then action else principal) has "C")) && false
};
