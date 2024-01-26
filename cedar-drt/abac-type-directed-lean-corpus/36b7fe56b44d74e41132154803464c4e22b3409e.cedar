@BM("")
@L("")
permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ((ip(principal["Bosp"])).isIpv4())) && false
};
