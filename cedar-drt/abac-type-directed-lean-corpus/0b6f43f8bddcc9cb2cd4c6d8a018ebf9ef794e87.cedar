@huuuuuu0("66")
permit(
  principal in a::"\n\n\n\n",
  action in [Action::"action"],
  resource is a in a::"\n\n\n\n"
) when {
  (true && ((ip(resource["P"])).isIpv4())) && ((ip(principal["P"])).isIpv4())
};
