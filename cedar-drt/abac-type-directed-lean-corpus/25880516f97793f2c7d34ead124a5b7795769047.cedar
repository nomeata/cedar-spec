permit(
  principal,
  action,
  resource
) when {
  (true && (C::"666[" in resource)) && ((if ((ip("54.54.54.54")).isMulticast()) then 1533306667209 else 0) == 0)
};
