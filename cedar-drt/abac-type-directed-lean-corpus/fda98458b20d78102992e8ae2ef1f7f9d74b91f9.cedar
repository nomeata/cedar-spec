permit(
  principal is a in a::"v66",
  action in [Action::"action"],
  resource is a in a::"v66"
) when {
  (true && ((if ((ip("249.0.54.17/188")).isIpv4()) then (ip("")) else (ip(""))).isIpv6())) && (a::"v66" has "\u{6}")
};
