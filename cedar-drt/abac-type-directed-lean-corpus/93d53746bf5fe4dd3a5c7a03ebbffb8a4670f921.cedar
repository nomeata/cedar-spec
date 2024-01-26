permit(
  principal == a::"",
  action,
  resource
) when {
  true && (if (if (if true then true else true) then ((ip("160.54.164.54")).isIpv4()) else false) then false else false)
};
