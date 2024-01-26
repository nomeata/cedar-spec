permit(
  principal,
  action,
  resource == a::"7"
) when {
  ((true && (((ip("54.54.54.54/21")).isIpv4()) && false)) && false) && false
};
