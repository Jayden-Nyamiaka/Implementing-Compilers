# Run single-pass tests in order.

for pass in lwhile sh un ug rc ec tc2 ru si ul ; do
  python3 scripts/compare.py -diff reference/*.$pass
  echo
  read -p 'next...'
  echo
done

for pass in bi ar rj pi pc ; do
  python3 scripts/compare.py -diff reference/*.$pass*
  echo
  read -p 'next...'
  echo
done
