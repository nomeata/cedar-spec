permit(
  principal is a in a::"\"146",
  action in [Action::"action"],
  resource is a in a::"\"146"
) when {
  (true && ((if ((ip("54.50.54.54")).isLoopback()) then 72056649145070114 else 2475009470216798463) == 3906365871525671458)) && ((ip("")).isIpv4())
};
