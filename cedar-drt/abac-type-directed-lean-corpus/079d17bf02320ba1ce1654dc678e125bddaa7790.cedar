permit(
  principal is a in a::"66766\0",
  action in [Action::"v6z3"],
  resource is a in a::"66766\0"
) when {
  ((true && ((if ("6" == "") then (ip("::636:74ca:3636")) else (ip("0.0.0.0"))).isIpv4())) && false) && false
};
