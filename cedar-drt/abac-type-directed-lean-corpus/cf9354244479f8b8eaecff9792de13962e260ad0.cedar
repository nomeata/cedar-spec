@A("")
permit(
  principal,
  action,
  resource is a in a::"66663ef\0"
) when {
  (true && (a::"66666" in principal)) && ((ip("")).isIpv4())
};
