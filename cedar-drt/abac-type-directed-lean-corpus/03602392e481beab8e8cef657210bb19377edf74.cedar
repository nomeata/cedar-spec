permit(
  principal == a::"",
  action,
  resource == a::"\0626\u{1}"
) when {
  true && (((ip("6&66666")).isIpv4()) || false)
};
