permit(
  principal,
  action,
  resource
) when {
  (true && (!(!((ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:c9c9/54")).isMulticast())))) && false
};
