permit(
  principal,
  action,
  resource is a in a::"6"
) when {
  true && ([(ip("93.54.54.54/11")).isIpv4(), false, false].contains(false))
};
