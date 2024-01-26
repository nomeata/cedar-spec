permit(
  principal,
  action,
  resource
) when {
  (true && (!(!((ip("::ff:ffff:ffff:0:3627:c9c9")).isMulticast())))) && false
};
