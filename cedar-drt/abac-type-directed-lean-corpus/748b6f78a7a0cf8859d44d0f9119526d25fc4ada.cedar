permit(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  true && ((resource["Bnss"]).isIpv4())
};
