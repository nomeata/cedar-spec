permit(
  principal,
  action,
  resource
) when {
  (true && ((if ((ip("54.54.255.200")).isInRange(ip("0.0.0.0"))) then principal else principal) has "sIIs")) && false
};
