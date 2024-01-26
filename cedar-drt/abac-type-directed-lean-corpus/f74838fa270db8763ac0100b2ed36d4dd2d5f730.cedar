permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::"6]6"
) when {
  (true && ((if false then (ip("")) else (ip(""))).isIpv4())) && (!(if (principal in action) then (!false) else (!false)))
};
