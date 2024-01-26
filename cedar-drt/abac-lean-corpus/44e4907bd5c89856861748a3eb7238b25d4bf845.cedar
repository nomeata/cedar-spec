permit(
  principal,
  action,
  resource == a::""
) when {
  (true && (!(if principal then principal else (context == a::"jhjj")))) && (!(!(!a::"")))
};
